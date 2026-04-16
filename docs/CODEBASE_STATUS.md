# Codebase Status

Last refreshed: 2026-04-16 (Europe/Sofia)

## Verified Repository Snapshot

- Branch: `main`
- HEAD: `a1bf797074a523f813d98cb6af18552080ac733b`
- Commit title: `Add co-owner modular Hamiltonian doubled bridge and Preg support bridge`

## Verification Gates

The following checks were executed successfully (exit code `0`):

1. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.ModularHamiltonianDoubledBridge`
2. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All`
3. `/bin/bash -lc PYTHONPATH=. lake script run strictCheck`

## Canonical Status Highlights

- The doubled modular Hamiltonian translator/coherence surface is present and build-verified:
  - `lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean`
- The support-restricted companion bridge is present and build-verified:
  - `lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean`
- The signed-particle translator lane is present in canonical imports:
  - `lean/InfoGeometry/Canonical/SignedParticleBridge.lean`
- The Arnold-network presentation bridge is present in canonical imports:
  - `lean/InfoGeometry/Canonical/ArnoldNetworkPresentation.lean`
- Canonical umbrella import is active:
  - `lean/InfoGeometry/Canonical/All.lean`
- Candidate bridge packet intake lane is present:
  - `tools/schema/candidate_bridge_packet.json`
  - `tools/infra/candidate_bridge_packet.py`
  - `docs/CandidateBridgePacketContract.md`

## Documentation Sync Snapshot

This status refresh aligns the active markdown entry surfaces with current
canonical state:

- all tracked `README*.md` files point to this status file;
- modular-map docs now include the doubled modular Hamiltonian bridge lane;
- docs index now includes the new co-owner black-book closure note.

## DAG Artifact Snapshot

From `artifacts/dag/index/meta.json`:

- `schemaVersion`: `3`
- `timestamp`: `2026-04-15T22:06:28.722846+00:00`
- `nodeCount`: `17945`
- `edgeCount`: `149817`
- `oleanHash`: `43f327054d34dbf35f81d2319cd264a7f27409ac136f9bcdd5ee0e74d0837ff0`

## Documentation Rule

Use this file as the operational status source for README/doc surfaces.
When status changes, update this file first, then README/doc links.

Truth order remains:

1. Lean source under `lean/InfoGeometry/`
2. `lean/InfoGeometry/Audit.lean` and `lean/InfoGeometry/Meta/Architecture.lean`
3. DAG atomic artifacts under `artifacts/dag/`
4. Reports and narrative docs
