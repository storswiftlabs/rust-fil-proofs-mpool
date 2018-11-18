use api::sector_builder::errors::*;
use api::sector_builder::metadata::sum_piece_bytes;
use api::sector_builder::metadata::StagedSectorMetadata;
use api::sector_builder::state::StagedState;
use api::sector_builder::*;
use error;
use sector_base::api::disk_backed_storage::ConcreteSectorStore;
use sector_base::api::sector_store::SectorManager;
use sector_base::api::sector_store::SectorStore;
use std::sync::Arc;
use std::sync::MutexGuard;

pub fn add_piece<S: Into<String>>(
    sector_store: &Arc<ConcreteSectorStore>,
    mut staged_state: &mut MutexGuard<StagedState>,
    piece_key: S,
    piece_bytes: &[u8],
) -> error::Result<SectorId> {
    let sector_store = sector_store.clone();
    let sector_mgr = sector_store.manager();
    let sector_max = sector_store.config().max_unsealed_bytes_per_sector();

    let piece_bytes_len = piece_bytes.len() as u64;

    let opt_dest_sector_id = {
        let candidates: Vec<StagedSectorMetadata> = staged_state
            .sectors
            .iter()
            .filter(|(k, _)| staged_state.sectors_accepting_data.contains(k))
            .map(|(_, v)| (*v).clone())
            .collect();

        compute_destination_sector_id(&candidates[..], sector_max, piece_bytes_len)?
    };

    let dest_sector_id = opt_dest_sector_id
        .ok_or(())
        .or_else(|_| provision_new_staged_sector(sector_mgr, &mut staged_state))?;

    if let Some(s) = staged_state.sectors.get_mut(&dest_sector_id) {
        sector_store
            .manager()
            .write_and_preprocess(s.sector_access.clone(), &piece_bytes)
            .map_err(|err| err.into())
            .and_then(|num_bytes_written| {
                if num_bytes_written != piece_bytes_len {
                    Err(err_inc_write(num_bytes_written, piece_bytes_len).into())
                } else {
                    Ok(s.sector_id)
                }
            })
            .map(|sector_id| {
                s.pieces.push(metadata::PieceMetadata {
                    piece_key: piece_key.into(),
                    num_bytes: piece_bytes_len,
                });

                sector_id
            })
    } else {
        Err(err_unrecov("unable to retrieve sector from state-map").into())
    }
}

// Given a list of staged sectors which are accepting data, return the
// first staged sector into which the bytes will fit.
fn compute_destination_sector_id(
    candidate_sectors: &[StagedSectorMetadata],
    max_bytes_per_sector: u64,
    num_bytes_in_piece: u64,
) -> error::Result<Option<u64>> {
    if num_bytes_in_piece > max_bytes_per_sector {
        Err(err_overflow(num_bytes_in_piece, max_bytes_per_sector).into())
    } else {
        Ok(candidate_sectors
            .iter()
            .find(move |staged_sector| {
                (max_bytes_per_sector - sum_piece_bytes(staged_sector)) > num_bytes_in_piece
            })
            .map(|x| x.sector_id))
    }
}

// Provisions a new staged sector and returns its sector_id. Not a pure
// function; creates a sector access (likely a file), increments the sector id
// nonce, and mutates the StagedState.
fn provision_new_staged_sector(
    sector_manager: &SectorManager,
    locked_state: &mut MutexGuard<StagedState>,
) -> error::Result<SectorId> {
    let sector_id = {
        let mut n = &mut locked_state.sector_id_nonce;
        *n += 1;
        *n
    };

    let access = sector_manager.new_staging_sector_access()?;

    let meta = StagedSectorMetadata {
        pieces: Default::default(),
        sealing_error: None,
        sector_access: access.clone(),
        sector_id,
    };

    locked_state.sectors_accepting_data.insert(meta.sector_id);
    locked_state.sectors.insert(meta.sector_id, meta.clone());

    Ok(sector_id)
}