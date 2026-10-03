# Legacy Archive

> Status: `archival reference`
> Audited: 2026-05-02
> Note: Kept for provenance and archaeology, not as current policy.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

This directory holds historical automation scripts and scratch Lean files kept
for provenance, but removed from the active build and supported automation
surface.

They may still contain useful ideas, partial workflows, or abandoned proof
search directions. Treat them as design archaeology, not as current entrypoints.

Current authoritative automation lives in:

- `tools/frontier/semantic_block_export.py`
- `tools/frontier/skynet_v2.py`
- `tools/docs/generate_auto_docs.py`
- `tools/docs/update_repo_docs.py`

Current active Lean tooling lives primarily in:

- `lean/DAG`
- `lean/scripts/DAG/Exploration`

Archived here:

- legacy autonomous proof-discovery scripts from the old `skynet` path
- legacy graph/bootstrap blueprint generators archived from `scripts/` and `scripts/docs/`
- archived docs-map/module-graph compatibility lane (`make_graph.py`, `refactor_plan.py`, and `GraphExport.lean`)
- archived declaration-graph wrapper now served through `tools/graph.py` as a compatibility shim
- dummy, timeout-probe, and duplicate-shadow Lean files removed from the package build surface

Practical rule:

- mine this directory for ideas or historical context;
- do not route new automation through it unless you are intentionally reviving
  an old line of work.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md) for the current build/audit state.
