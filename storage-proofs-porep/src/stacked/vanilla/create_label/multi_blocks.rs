use std::convert::TryInto;
use std::marker::PhantomData;
use std::mem::{self, size_of, ManuallyDrop};
use std::sync::{
    atomic::{AtomicU64, Ordering::SeqCst},
    Arc, MutexGuard, Mutex, Condvar,
};
use std::thread;
use std::thread::ThreadId;
use std::time::Duration;
use std::ptr;
use std::fs::{self, create_dir_all, rename};
use std::fs::OpenOptions;
use std::io::Write;
use lazy_static::lazy_static;
use std::cell::UnsafeCell;

use anyhow::{Context, Result};
use byte_slice_cast::{AsByteSlice, AsMutSliceOf};
use filecoin_hashers::Hasher;
use generic_array::{
    typenum::{Unsigned, U64},
    GenericArray,
};
use log::{debug, info};
use mapr::MmapMut;
use merkletree::store::{DiskStore, Store, StoreConfig};
use storage_proofs_core::{
    cache_key::CacheKey,
    drgraph::{Graph, BASE_DEGREE},
    merkle::MerkleTreeTrait,
    settings::SETTINGS,
    util::NODE_SIZE,
};

use crate::stacked::vanilla::{
    cache::ParentCache,
    cores::{bind_core, checkout_core_group, CoreIndex},
    create_label::{prepare_layers, read_layer, write_layer},
    graph::{StackedBucketGraph, DEGREE, EXP_DEGREE},
    memory_handling::{setup_create_label_memory, CacheReader},
    params::{Labels, LabelsCache},
    proof::LayerState,
    utils::{memset, prepare_block, BitMask, RingBuf, UnsafeSlice},
};
use std::path::Path;
use std::collections::HashMap;
use std::env;

//extern crate libc;


const MIN_BASE_PARENT_NODE: u64 = 2000;

const WORD_SIZE: usize = size_of::<u32>();
const NODE_WORDS: usize = NODE_SIZE / size_of::<u32>();
const SHA_BLOCK_SIZE: usize = 64;

const SHA256_INITIAL_DIGEST: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

// minmum: S * (m + 1)
// midium: S * (3m + 1) / 2
// maxmum: S * 2m
//
// count = 512M/32M * (3*6+1)/2 = 16 * 19 / 2 = 152
//
lazy_static! {
     pub static ref LABEL_POOL_PAIR: Arc<(Mutex<LabelPool>, Condvar)> = Arc::new((Mutex::new(LabelPool::new()), Condvar::new()));
     pub static ref SECTOR_SIZE: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));
}

pub struct LabelPool {
    pub sector:     usize,
    pub tasks:      usize,
    pub block:      usize,
    pub count:      usize,
    pub total:      usize,

    pub maxidx:     usize,
    pub tidmap:     HashMap<ThreadId, usize>,
    pub idxmap:     Vec<usize>,
    pub banks:      Vec<usize>,
    pub pool:       Vec<u8>,
}

impl LabelPool {
    pub fn new() -> Self {
        let mut sector = *SECTOR_SIZE.lock().unwrap();
        //let sector: usize = SETTINGS.sector_size;

        let tasks: usize = SETTINGS.p1_tasks;

        let block: usize = SETTINGS.p1_block;
        let count: usize = sector / block;

        let total: usize = if env::var("FIL_PROOFS_P1_TOTAL").is_ok() {
            SETTINGS.p1_total
        } else {
            // avaiable = total - cache
            (tasks * 3 + 1) * sector / 2 / block
        };
        let pool_size: usize = block * total;

        info!("PPERF: tasks={} total={}, steps={}", tasks, total, count);
        assert!(pool_size > sector * (tasks + 1), "Pool size must great than minimum margin!!!");

        // medium : sector * (tasks * 3 + 1) / 2
        // minimum: sector * (tasks + 1)
        // maximum: sector * (tasks * 2)
        //assert!(pool_size >= sector * (tasks + 1));
        //assert!(pool_size <= sector * tasks * 2);

        Self {
            sector,
            tasks,
            block,
            count,
            total,
            maxidx: 0,
            tidmap: HashMap::new(),
            idxmap: vec![0; total],
            banks: {
                let mut v: Vec<usize> = (0..total).collect();
                v.reverse();
                v
            },
            pool: create_pool(pool_size),
        }
    }

    pub fn available(&self, preindex: usize) -> bool {
        // find out max index
        let spare = self.count - self.maxidx;

        self.banks.len() > 0 && (self.banks.len() > spare || preindex + 1 > self.maxidx)
    }

    pub fn acquire(&mut self, tid: ThreadId, index: usize) -> Option<ManuallyDrop<Vec<u8>>> {
        assert!(index < self.total);

        //if !self.available() {
        //    return None;
        //}

        let idx = self.banks.pop().unwrap();
        let buf = unsafe {
            let ptr = self.pool.as_ptr().offset((self.block * idx) as isize) as usize;
            self.idxmap[idx] = index + 1;
            self.tidmap.insert(tid, index + 1);

            // find max index from tidmap
            let mut v = self.tidmap.values().copied().collect::<Vec<_>>();
            v.sort();
            self.maxidx = v.pop().unwrap();

            Vec::from_raw_parts(ptr as *mut u8, self.block, self.block)
        };

        Some(ManuallyDrop::new(buf))
    }

    pub fn release(&mut self, tid: ThreadId, buf: &mut Vec<ManuallyDrop<Vec<u8>>>) {
        for _ in 0..buf.len() {
            let v = buf.pop().unwrap();
            let ptr = v.as_ptr();
            let len = unsafe { ptr.offset_from(self.pool.as_ptr()) };

            assert!(len >= 0);
            let idx = len as usize / self.block;

            // recycle memory
            self.banks.push(idx);

            // recycle index map position
            self.idxmap[idx] = 0;

            // remove tid
            self.tidmap.remove(&tid);

            // find max index from tidmap
            let mut v = self.tidmap.values().copied().collect::<Vec<_>>();
            self.maxidx = if v.len() > 0 {
                v.sort();
                v.pop().unwrap()
            } else {
                0
            };
        }
    }

}

impl Drop for LabelPool {
    fn drop(&mut self) {
        let old = mem::take(&mut self.pool);
        destroy_pool(old);
    }
}

// Allocate label pool
fn create_pool(pool_size: usize) -> Vec<u8> {
    info!("PPERF: alloc pool");
    unsafe {
        let data = libc::mmap(ptr::null_mut(), pool_size, libc::PROT_READ|libc::PROT_WRITE, libc::MAP_PRIVATE|libc::MAP_ANONYMOUS, -1, 0);
        if data == libc::MAP_FAILED {
            panic!("PPERF: out of memory");
        }
        info!("PPERF: alloc buffer {:p}, len={}", data, pool_size);
        Vec::from_raw_parts(data as *mut u8, pool_size, pool_size)
    }
}

// Free label pool
fn destroy_pool(buf: Vec<u8>) {
    unsafe {
        info!("PPERF: free buffer {:p}, len={}", buf.as_ptr(), buf.len());
        libc::munmap(buf.as_ptr() as *mut libc::c_void, buf.len());
    }
    core::mem::forget(buf);
}

fn alloc_block(tid: ThreadId, idx: usize) -> Option<ManuallyDrop<Vec<u8>>> {
    let (lock, cond) = &**LABEL_POOL_PAIR;
    let mut pool = lock.lock().unwrap();

    while !pool.available(idx) {
        pool = cond.wait(pool).unwrap();
    }

    let label = pool.acquire(tid, idx);

    label
}

fn free_block(tid: ThreadId, buf: &mut Vec<ManuallyDrop<Vec<u8>>>) {
    let (lock, cond) = &**LABEL_POOL_PAIR;
    let mut pool = lock.lock().unwrap();

    pool.release(tid, buf);
    cond.notify_all();
}


pub struct LayerBlocks {
    block_tid: ThreadId,
    block_nodes: usize,
    block_words: usize,
    block_bytes: usize,
    blocks: Vec<ManuallyDrop<Vec<u8>>>,
}

impl LayerBlocks {
    pub fn new(sector: usize) -> Self {
        // sync sector size
        *SECTOR_SIZE.lock().unwrap() = sector;

        let (lock, _cond) = &**LABEL_POOL_PAIR;
        let pool = lock.lock().unwrap();
        let count = pool.sector / pool.block;

        Self {
            block_tid: thread::current().id(),
            block_nodes: pool.block / NODE_SIZE,
            block_words: pool.block / WORD_SIZE,
            block_bytes: pool.block,
            blocks: Vec::with_capacity(count),
        }
    }

    pub fn get_block_nodes(&self) -> usize {
        self.block_nodes
    }

    pub fn get_block_words(&self) -> usize {
        self.block_words
    }

    pub fn get_block_bytes(&self) -> usize {
        self.block_bytes
    }

    pub fn get_blocks_len(&self) -> usize {
        self.blocks.len()
    }

    pub fn get_block(&self, idx: usize) -> &[u8] {
        &self.blocks[idx]
    }

    pub fn is_boundary(&self, node: u64) -> bool {
        node % self.block_nodes as u64 == 0
    }

    pub fn acquire_node(&mut self, node: u64) -> ManuallyDrop<Vec<u32>> {
        let idx = node as usize / self.block_nodes;

        {
            let (lock, cond) = &**LABEL_POOL_PAIR;
            let mut pool = lock.lock().unwrap();

            if idx >= self.blocks.len() {
                while !pool.available(idx) {
                    info!("wait block node: {:?}", thread::current().id());
                    pool = cond.wait(pool).unwrap();
                    info!("get block node: {:?}", thread::current().id());
                }

                if idx >= self.blocks.len() {
                    let mem = pool.acquire(self.block_tid, idx);
                    self.blocks.push(mem.unwrap());
                }
            }
        }

        let offset = (node as usize % self.block_nodes) * NODE_WORDS;
        let ptr = self.blocks[idx].as_mut_slice_of::<u32>().unwrap().as_mut_ptr();

        ManuallyDrop::new(unsafe { Vec::from_raw_parts(ptr.offset(offset as isize), NODE_WORDS, NODE_WORDS) })
    }

    pub fn acquire_node_sure(&mut self, node: u64) -> ManuallyDrop<Vec<u32>> {
        let idx = node as usize / self.block_nodes;
        assert!(idx < self.blocks.len());

        let offset = (node as usize % self.block_nodes) * NODE_WORDS;
        let ptr = self.blocks[idx].as_mut_slice_of::<u32>().unwrap().as_mut_ptr();

        ManuallyDrop::new(unsafe { Vec::from_raw_parts(ptr.offset(offset as isize), NODE_WORDS, NODE_WORDS) })
    }

    // !!! Special case on blocks len test, because block free at layer done time.
    pub fn acquire_node_vec(&mut self, node: u64) -> ManuallyDrop<Vec<u32>> {
        let idx = node as usize / self.block_nodes;

        {
            let (lock, cond) = &**LABEL_POOL_PAIR;
            let mut pool = lock.lock().unwrap();

            if idx >= self.blocks.len() {
                while !pool.available(idx) {
                    info!("wait block vec: {:?}", thread::current().id());
                    pool = cond.wait(pool).unwrap();
                    info!("get block vec: {:?}", thread::current().id());
                }

                if idx >= self.blocks.len() {
                    let mem = pool.acquire(self.block_tid, idx);
                    self.blocks.push(mem.unwrap());
                }
            }
        }

        let ptr = self.blocks[idx].as_mut_slice_of::<u32>().unwrap().as_mut_ptr();

        ManuallyDrop::new(unsafe { Vec::from_raw_parts(ptr, self.block_words, self.block_words) })
    }

    pub fn acquire_node_slice(&mut self, node: u64) -> ManuallyDrop<Vec<u32>> {
        let idx = node as usize / self.block_nodes;

        {
            let (lock, cond) = &**LABEL_POOL_PAIR;
            let mut pool = lock.lock().unwrap();

            if idx >= self.blocks.len() {
                while !pool.available(idx) {
                    info!("wait block slice: {:?}", thread::current().id());
                    pool = cond.wait(pool).unwrap();
                    info!("get block slice: {:?}", thread::current().id());
                }

                if idx >= self.blocks.len() {
                    let mem = pool.acquire(self.block_tid, idx);
                    self.blocks.push(mem.unwrap());
                }
            }
        }

        let offset = (node as usize % self.block_nodes) * NODE_WORDS;
        let remain = self.block_words - offset;

        let ptr = self.blocks[idx].as_mut_slice_of::<u32>().unwrap().as_mut_ptr();

        ManuallyDrop::new(unsafe { Vec::from_raw_parts(ptr.offset(offset as isize), remain, remain) })
    }


    pub fn free(&mut self) {
        free_block(self.block_tid, &mut self.blocks);
        self.blocks.clear();
    }

}

impl Drop for LayerBlocks {
    fn drop(&mut self) {
        free_block(self.block_tid, &mut self.blocks);
    }
}


pub struct UnsafeBlocks<'a, T> {
    // holds the data to ensure lifetime correctness
    data: &'a UnsafeCell<T>,
}

unsafe impl<'a, T> Sync for UnsafeBlocks<'a, T> {}

impl<'a, T> UnsafeBlocks<'a, T> {
    // Takes mutable slice, to ensure that `UnsafeSlice` is the only user of this memory, until it
    // gets dropped.
    pub fn new(source: &'a mut T) -> Self {
        let ptr = source as *mut T as *const UnsafeCell<T>;
        Self {
            data: unsafe { &*ptr },
        }
    }

    // Safety: The caller must ensure that there are no unsynchronized parallel access to the same
    // regions.
    #[inline]
    pub unsafe fn get(&self) -> &'a mut T {
        &mut *self.data.get()
    }
}


/// Stores a layer atomically on disk, by writing first to `.tmp` and then renaming.
fn write_layer_blocks(blocks: &UnsafeBlocks<'_, LayerBlocks>, config: &StoreConfig) -> Result<()> {
    let data_path = StoreConfig::data_path(&config.path, &config.id);
    let tmp_data_path = data_path.with_extension("tmp");

    if let Some(parent) = data_path.parent() {
        create_dir_all(parent).context("failed to create parent directories")?;
    }

    let layer_blocks = unsafe { blocks.get() };
    let num = layer_blocks.get_blocks_len();

    let mut file = OpenOptions::new().append(true)
                                     .create(true)
                                     .open(&tmp_data_path)?;
    for i in 0..num {
        file.write_all(layer_blocks.get_block(i)).context("failed to write layer data")?;
    }
    rename(tmp_data_path, data_path).context("failed to rename tmp data")?;

    Ok(())
}



#[inline]
fn fill_buffer(
    cur_node_ptr: &mut [u32],
    cur_node: u64,
    parents_cache: &CacheReader<u32>,
    mut cur_parent: &[u32], // parents for this node
    layer_labels: &UnsafeBlocks<'_, LayerBlocks>,
    exp_labels: Option<&UnsafeBlocks<'_, LayerBlocks>>, // None for layer0
    buf: &mut [u8],
    base_parent_missing: &mut BitMask,
) {
    let cur_node_swap = cur_node.to_be_bytes(); // Note switch to big endian
    buf[36..44].copy_from_slice(&cur_node_swap); // update buf with current node

    // Perform the first hash
    cur_node_ptr[..8].copy_from_slice(&SHA256_INITIAL_DIGEST);
    compress256!(cur_node_ptr, buf, 1);

    //core::mem::forget(cur_node_ptr);
    let layer_labels = unsafe { layer_labels.get() };

    // Fill in the base parents
    // Node 5 (prev node) will always be missing, and there tend to be
    // frequent close references.
    if cur_node > MIN_BASE_PARENT_NODE {
        // Mark base parent 5 as missing
        // base_parent_missing.set_all(0x20);
        base_parent_missing.set(5);

        // Skip the last base parent - it always points to the preceding node,
        // which we know is not ready and will be filled in the main loop
        for k in 0..BASE_DEGREE - 1 {
            unsafe {
                if cur_parent[0] as u64 >= parents_cache.get_consumer() {
                    // Node is not ready
                    base_parent_missing.set(k);
                } else {
                    let parent_data = layer_labels.acquire_node_sure(cur_parent[0] as u64);
                    let a = SHA_BLOCK_SIZE + (NODE_SIZE * k);
                    buf[a..a + NODE_SIZE].copy_from_slice(parent_data.as_byte_slice());
                };

                // Advance pointer for the last base parent
                cur_parent = &cur_parent[1..];
            }
        }
        // Advance pointer for the last base parent
        cur_parent = &cur_parent[1..];
    } else {
        base_parent_missing.set_upto(BASE_DEGREE as u8);
        cur_parent = &cur_parent[BASE_DEGREE..];
    }

    if let Some(exp_labels) = exp_labels {
        let exp_labels = unsafe { exp_labels.get() };
        // Read from each of the expander parent nodes
        for k in BASE_DEGREE..DEGREE {
            let parent_data = exp_labels.acquire_node_sure(cur_parent[0] as u64);
            let a = SHA_BLOCK_SIZE + (NODE_SIZE * k);
            buf[a..a + NODE_SIZE].copy_from_slice(parent_data.as_byte_slice());
            cur_parent = &cur_parent[1..];
        }
    }
}

// This implements a producer, i.e. a thread that pre-fills the buffer
// with parent node data.
// - cur_consumer - The node currently being processed (consumed) by the
//                  hashing thread
// - cur_producer - The next node to be filled in by producer threads. The
//                  hashing thread can not yet work on this node.
// - cur_awaiting - The first not not currently being filled by any producer
//                  thread.
// - stride       - Each producer fills in this many nodes at a time. Setting
//                  this too small with cause a lot of time to be spent in
//                  thread synchronization
// - lookahead    - ring_buf size, in nodes
// - base_parent_missing - Bit mask of any base parent nodes that could not
//                         be filled in. This is an array of size lookahead.
// - is_layer0    - Indicates first (no expander parents) or subsequent layer
#[allow(clippy::too_many_arguments)]
fn create_label_runner(
    parents_cache: &CacheReader<u32>,
    layer_labels: &UnsafeBlocks<'_, LayerBlocks>,
    exp_labels: Option<&UnsafeBlocks<'_, LayerBlocks>>, // None for layer 0
    num_nodes: u64,
    cur_producer: &AtomicU64,
    cur_awaiting: &AtomicU64,
    stride: u64,
    lookahead: u64,
    ring_buf: &RingBuf,
    base_parent_missing: &UnsafeSlice<'_, BitMask>,
) {
    info!("created label runner");
    // Label data bytes per node
    let layer_block = unsafe { layer_labels.get() };
    let block_nodes = layer_block.get_block_nodes();
    let mut block: ManuallyDrop<Vec<u32>> = ManuallyDrop::new(Vec::new());
    let mut last_work = 0u64;
    let mut remain = 0u64;
    let mut cur_node_ptr: &mut [u32];

    loop {
        // Get next work items
        let work = cur_awaiting.fetch_add(stride, SeqCst);
        if work >= num_nodes {
            break;
        }
        let count = if work + stride > num_nodes {
            num_nodes - work
        } else {
            stride
        };

        let offset = work - last_work;
        if offset >= remain {
            block = layer_block.acquire_node_slice(work);
            cur_node_ptr = &mut block[0..];
            last_work = work;
            remain = block_nodes as u64 - work % block_nodes as u64 - 1;
        } else {
            cur_node_ptr = &mut block[offset as usize * NODE_WORDS..];
            remain -= work - last_work;
        }

        // Do the work of filling the buffers
        for cur_node in work..work + count {
            // Determine which node slot in the ring_buffer to use
            // Note that node 0 does not use a buffer slot
            let cur_slot = (cur_node - 1) % lookahead;

            // Don't overrun the buffer
            while cur_node > (parents_cache.get_consumer() + lookahead - 1) {
                thread::sleep(Duration::from_micros(10));
            }

            let buf = unsafe { ring_buf.slot_mut(cur_slot as usize) };
            let bpm = unsafe { base_parent_missing.get_mut(cur_slot as usize) };

            let pc = unsafe { parents_cache.slice_at(cur_node as usize * DEGREE as usize) };

            if cur_node % block_nodes as u64 == 0 {
                block = layer_block.acquire_node_slice(cur_node);
                cur_node_ptr = &mut block[0..];
                last_work = cur_node;
                remain = block_nodes as u64;
            }

            fill_buffer(
                cur_node_ptr,
                cur_node,
                parents_cache,
                pc,
                layer_labels,
                exp_labels,
                buf,
                bpm,
            );

            cur_node_ptr = &mut cur_node_ptr[8..];
        }

        // Wait for the previous node to finish
        while work > (cur_producer.load(SeqCst) + 1) {
            thread::sleep(Duration::from_micros(10));
        }

        // Mark our work as done
        cur_producer.fetch_add(count, SeqCst);
    }
}

fn create_layer_labels<Tree: 'static + MerkleTreeTrait>(
    graph: &StackedBucketGraph<Tree::Hasher>,
    parents_cache: &CacheReader<u32>,
    replica_id: &[u8],
    layer_labels: &UnsafeBlocks<'_, LayerBlocks>,
    exp_labels: Option<&UnsafeBlocks<'_, LayerBlocks>>,
    num_nodes: u64,
    cur_layer: u32,
    core_group: Arc<Option<MutexGuard<'_, Vec<CoreIndex>>>>,
) {
    info!("Creating labels for layer {}", cur_layer);
    // num_producers is the number of producer threads
    let (lookahead, num_producers, producer_stride) = {
        let settings = &SETTINGS;
        let lookahead = settings.multicore_sdr_lookahead;
        let num_producers = settings.multicore_sdr_producers;
        // NOTE: Stride must not exceed the number of nodes in parents_cache's window. If it does, the process will deadlock
        // with producers and consumers waiting for each other.
        let producer_stride = settings
            .multicore_sdr_producer_stride
            .min(parents_cache.window_nodes() as u64);

        (lookahead, num_producers, producer_stride)
    };

    const BYTES_PER_NODE: usize = (NODE_SIZE * DEGREE) + SHA_BLOCK_SIZE;

    let mut ring_buf = RingBuf::new(BYTES_PER_NODE, lookahead);
    let mut base_parent_missing = vec![BitMask::default(); lookahead];

    // Fill in the fixed portion of all buffers
    for buf in ring_buf.iter_slot_mut() {
        prepare_block(replica_id, cur_layer, buf);
    }

    // Highest node that is ready from the producer
    let cur_producer = AtomicU64::new(0);
    // Next node to be filled
    let cur_awaiting = AtomicU64::new(1);

    // These UnsafeSlices are managed through the 3 Atomics above, to minimize any locking overhead.
    let base_parent_missing = UnsafeSlice::from_slice(&mut base_parent_missing);

    crossbeam::thread::scope(|s| {
        let mut runners = Vec::with_capacity(num_producers);

        for i in 0..num_producers {
            let cur_producer = &cur_producer;
            let cur_awaiting = &cur_awaiting;
            let ring_buf = &ring_buf;
            let base_parent_missing = &base_parent_missing;

            let core_index = if let Some(cg) = &*core_group {
                cg.get(i + 1)
            } else {
                None
            };
            runners.push(s.spawn(move |_| {
                // This could fail, but we will ignore the error if so.
                // It will be logged as a warning by `bind_core`.
                debug!("binding core in producer thread {}", i);
                // When `_cleanup_handle` is dropped, the previous binding of thread will be restored.
                let _cleanup_handle = core_index.map(|c| bind_core(*c));

                create_label_runner(
                    parents_cache,
                    layer_labels,
                    exp_labels,
                    num_nodes,
                    cur_producer,
                    cur_awaiting,
                    producer_stride,
                    lookahead as u64,
                    ring_buf,
                    base_parent_missing,
                )
            }));
        }

        let layer_labels = unsafe { layer_labels.get() };
        let (mut cur_node_vec, block_nodes) = {
            (layer_labels.acquire_node_vec(0), layer_labels.get_block_nodes())
        };
        let mut cur_node_ptr = &mut cur_node_vec[0..];
        let mut cur_parent_ptr = unsafe { parents_cache.consumer_slice_at(DEGREE) };
        let mut cur_parent_ptr_offset = DEGREE;

        // Calculate node 0 (special case with no parents)
        // Which is replica_id || cur_layer || 0
        // TODO - Hash and save intermediate result: replica_id || cur_layer
        let mut buf = [0u8; (NODE_SIZE * DEGREE) + 64];
        prepare_block(replica_id, cur_layer, &mut buf);

        cur_node_ptr[..8].copy_from_slice(&SHA256_INITIAL_DIGEST);
        compress256!(cur_node_ptr, buf, 2);

        // Fix endianess
        cur_node_ptr[..8].iter_mut().for_each(|x| *x = x.to_be());

        cur_node_ptr[7] &= 0x3FFF_FFFF; // Strip last two bits to ensure in Fr

        // Keep track of which node slot in the ring_buffer to use
        let mut cur_slot = 0;
        let mut count_not_ready = 0;

        // Calculate nodes 1 to n

        // Skip first node.
        parents_cache.store_consumer(1);
        let mut i = 1;
        while i < num_nodes {
            // Ensure next buffer is ready
            let mut counted = false;
            let mut producer_val = cur_producer.load(SeqCst);

            while producer_val < i {
                if !counted {
                    counted = true;
                    count_not_ready += 1;
                }
                thread::sleep(Duration::from_micros(10));
                producer_val = cur_producer.load(SeqCst);
            }

            // Process as many nodes as are ready
            let ready_count = producer_val - i + 1;
            for _count in 0..ready_count {
                // If we have used up the last cache window's parent data, get some more.
                if cur_parent_ptr.is_empty() {
                    // Safety: values read from `cur_parent_ptr` before calling `increment_consumer`
                    // must not be read again after.
                    unsafe {
                        cur_parent_ptr = parents_cache.consumer_slice_at(cur_parent_ptr_offset);
                    }
                }

                if i % block_nodes as u64 == 0 {
                    cur_node_vec = layer_labels.acquire_node_vec(i);
                    cur_node_ptr = &mut cur_node_vec;
                } else {
                    cur_node_ptr = &mut cur_node_ptr[8..];
                }

                // Grab the current slot of the ring_buf
                let buf = unsafe { ring_buf.slot_mut(cur_slot) };
                // Fill in the base parents
                for k in 0..BASE_DEGREE {
                    let bpm = unsafe { base_parent_missing.get(cur_slot) };
                    if bpm.get(k) {
                        let source = layer_labels.acquire_node_sure(cur_parent_ptr[0] as u64);

                        buf[64 + (NODE_SIZE * k)..64 + (NODE_SIZE * (k + 1))]
                            .copy_from_slice(source.as_byte_slice());
                    }
                    cur_parent_ptr = &cur_parent_ptr[1..];
                    cur_parent_ptr_offset += 1;
                }

                // Expanders are already all filled in (layer 1 doesn't use expanders)
                cur_parent_ptr = &cur_parent_ptr[EXP_DEGREE..];
                cur_parent_ptr_offset += EXP_DEGREE;

                if cur_layer == 1 {
                    // Six rounds of all base parents
                    for _j in 0..6 {
                        compress256!(cur_node_ptr, &buf[64..], 3);
                    }

                    // round 7 is only first parent
                    memset(&mut buf[96..128], 0); // Zero out upper half of last block
                    buf[96] = 0x80; // Padding
                    buf[126] = 0x27; // Length (0x2700 = 9984 bits -> 1248 bytes)
                    compress256!(cur_node_ptr, &buf[64..], 1);
                } else {
                    // Two rounds of all parents
                    let blocks = [
                        *GenericArray::<u8, U64>::from_slice(&buf[64..128]),
                        *GenericArray::<u8, U64>::from_slice(&buf[128..192]),
                        *GenericArray::<u8, U64>::from_slice(&buf[192..256]),
                        *GenericArray::<u8, U64>::from_slice(&buf[256..320]),
                        *GenericArray::<u8, U64>::from_slice(&buf[320..384]),
                        *GenericArray::<u8, U64>::from_slice(&buf[384..448]),
                        *GenericArray::<u8, U64>::from_slice(&buf[448..512]),
                    ];
                    sha2::compress256(
                        (&mut cur_node_ptr[..8])
                            .try_into()
                            .expect("compress failed"),
                        &blocks,
                    );
                    sha2::compress256(
                        (&mut cur_node_ptr[..8])
                            .try_into()
                            .expect("compress failed"),
                        &blocks,
                    );

                    // Final round is only nine parents
                    memset(&mut buf[352..384], 0); // Zero out upper half of last block
                    buf[352] = 0x80; // Padding
                    buf[382] = 0x27; // Length (0x2700 = 9984 bits -> 1248 bytes)
                    compress256!(cur_node_ptr, &buf[64..], 5);
                }

                // Fix endianess
                cur_node_ptr[..8].iter_mut().for_each(|x| *x = x.to_be());

                cur_node_ptr[7] &= 0x3FFF_FFFF; // Strip last two bits to fit in Fr

                // Safety:
                // It's possible that this increment will trigger moving the cache window.
                // In that case, we must not access `parents_cache` again but instead replace it.
                // This will happen above because `parents_cache` will now be empty, if we have
                // correctly advanced it so far.
                unsafe {
                    parents_cache.increment_consumer();
                }
                i += 1;
                cur_slot = (cur_slot + 1) % lookahead;
            }
        }

        debug!("PRODUCER NOT READY: {} times", count_not_ready);

        for runner in runners {
            runner.join().expect("join failed");
        }
    })
    .expect("crossbeam scope failure");
}

#[allow(clippy::type_complexity)]
pub fn create_labels_for_encoding<Tree: 'static + MerkleTreeTrait, T: AsRef<[u8]>>(
    graph: &StackedBucketGraph<Tree::Hasher>,
    parents_cache: &ParentCache,
    layers: usize,
    replica_id: T,
    config: StoreConfig,
) -> Result<(Labels<Tree>, Vec<LayerState>)> {
    info!("create labels");

    let layer_states = prepare_layers::<Tree>(graph, &config, layers);

    let sector_size = graph.size() * NODE_SIZE;
    let node_count = graph.size() as u64;
    let cache_window_nodes = SETTINGS.sdr_parents_cache_size as usize;

    let default_cache_size = DEGREE * 4 * cache_window_nodes;

    let core_group = Arc::new(checkout_core_group());

    // When `_cleanup_handle` is dropped, the previous binding of thread will be restored.
    let _cleanup_handle = (*core_group).as_ref().map(|group| {
        // This could fail, but we will ignore the error if so.
        // It will be logged as a warning by `bind_core`.
        debug!("binding core in main thread");
        group.get(0).map(|core_index| bind_core(*core_index))
    });

    // NOTE: this means we currently keep 2x sector size around, to improve speed
    let parents_cache = CacheReader::new(&parents_cache.path, Some(default_cache_size as usize), DEGREE)?;
    let mut cur_blocks = LayerBlocks::new(sector_size);
    let mut exp_blocks = LayerBlocks::new(sector_size);
    let layer_labels = UnsafeBlocks::new(&mut cur_blocks);
    let exp_labels = UnsafeBlocks::new(&mut exp_blocks);

    for (layer, layer_state) in (1..=layers).zip(layer_states.iter()) {
        info!("Layer {}", layer);

        if layer_state.generated {
            info!("skipping layer {}, already generated", layer);

            // load the already generated layer into exp_labels
            //read_layer(&layer_state.config, &mut exp_labels)?;
            continue;
        }

        // Cache reset happens in two parts.
        // The second part (the finish) happens before each layer but the first.
        if layers != 1 {
            parents_cache.finish_reset()?;
        }

        create_layer_labels::<Tree>(
            graph,
            &parents_cache,
            replica_id.as_ref(),
            &layer_labels,
            if layer == 1 {
                None
            } else {
                Some(&exp_labels)
            },
            node_count,
            layer as u32,
            core_group.clone(),
        );

        // Cache reset happens in two parts.
        // The first part (the start) happens after each layer but the last.
        if layer != layers {
            parents_cache.start_reset()?;
        }

        unsafe { std::mem::swap(&mut *layer_labels.get(), &mut *exp_labels.get()) };
        {
            let layer_config = &layer_state.config;

            info!("  storing labels on disk");
            write_layer_blocks(&exp_labels, layer_config).context("failed to store labels")?;

            info!(
                "generated layer {} store with id {} ",
                layer, layer_config.id
            );
        }
        unsafe { layer_labels.get().free() };
    }

    Ok((
        Labels::<Tree> {
            labels: layer_states.iter().map(|s| s.config.clone()).collect(),
            _h: PhantomData,
        },
        layer_states,
    ))
}

#[allow(clippy::type_complexity)]
pub fn create_labels_for_decoding<Tree: 'static + MerkleTreeTrait, T: AsRef<[u8]>>(
    graph: &StackedBucketGraph<Tree::Hasher>,
    parents_cache: &ParentCache,
    layers: usize,
    replica_id: T,
    config: StoreConfig,
) -> Result<LabelsCache<Tree>> {
    info!("create labels");

    // For now, we require it due to changes in encodings structure.
    let mut labels: Vec<DiskStore<<Tree::Hasher as Hasher>::Domain>> = Vec::with_capacity(layers);
    let mut label_configs: Vec<StoreConfig> = Vec::with_capacity(layers);

    let sector_size = graph.size() * NODE_SIZE;
    let node_count = graph.size() as u64;
    let cache_window_nodes = (&SETTINGS.sdr_parents_cache_size / 2) as usize;

    let default_cache_size = DEGREE * 4 * cache_window_nodes;

    let core_group = Arc::new(checkout_core_group());

    // When `_cleanup_handle` is dropped, the previous binding of thread will be restored.
    let _cleanup_handle = (*core_group).as_ref().map(|group| {
        // This could fail, but we will ignore the error if so.
        // It will be logged as a warning by `bind_core`.
        debug!("binding core in main thread");
        group.get(0).map(|core_index| bind_core(*core_index))
    });

    // NOTE: this means we currently keep 2x sector size around, to improve speed
    let parents_cache = CacheReader::new(&parents_cache.path, Some(default_cache_size as usize), DEGREE)?;
    let mut cur_blocks = LayerBlocks::new(sector_size);
    let mut exp_blocks = LayerBlocks::new(sector_size);
    let layer_labels = UnsafeBlocks::new(&mut cur_blocks);
    let exp_labels = UnsafeBlocks::new(&mut exp_blocks);

    for layer in 1..=layers {
        info!("Layer {}", layer);

        // Cache reset happens in two parts.
        // The second part (the finish) happens before each layer but the first.
        if layers != 1 {
            parents_cache.finish_reset()?;
        }

        create_layer_labels::<Tree>(
            graph,
            &parents_cache,
            replica_id.as_ref(),
            &layer_labels,
            if layer == 1 {
                None
            } else {
                Some(&exp_labels)
            },
            node_count,
            layer as u32,
            core_group.clone(),
        );

        // Cache reset happens in two parts.
        // The first part (the start) happens after each layer but the last.
        if layer != layers {
            parents_cache.start_reset()?;
        }

        //{
        //    let layer_config =
        //        StoreConfig::from_config(&config, CacheKey::label_layer(layer), Some(graph.size()));

        //    info!("  storing labels on disk");
        //    // Construct and persist the layer data.
        //    let layer_store: DiskStore<<Tree::Hasher as Hasher>::Domain> =
        //        DiskStore::new_from_slice_with_config(
        //            graph.size(),
        //            Tree::Arity::to_usize(),
        //            &layer_labels,
        //            layer_config.clone(),
        //        )?;
        //    info!(
        //        "  generated layer {} store with id {}",
        //        layer, layer_config.id
        //    );

        //    mem::swap(&mut layer_labels, &mut exp_labels);

        //    // Track the layer specific store and StoreConfig for later retrieval.
        //    labels.push(layer_store);
        //    label_configs.push(layer_config);
        //}
    }
    assert_eq!(
        labels.len(),
        layers,
        "Invalid amount of layers encoded expected"
    );

    Ok(LabelsCache::<Tree> { labels })
}

