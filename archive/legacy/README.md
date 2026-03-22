# Legacy Archive

This directory holds historical automation scripts and scratch Lean files kept
for provenance, but removed from the active build and supported automation
surface.

They may still contain useful ideas, partial workflows, or abandoned proof
search directions. Treat them as design archaeology, not as current entrypoints.

Current authoritative automation lives in:

- `tools/semantic_block_export.py`
- `tools/skynet_v2.py`
- `tools/generate_auto_docs.py`
- `tools/update_repo_docs.py`

Current active Lean tooling lives primarily in:

- `lean/DAG`
- `lean/scripts/DAG/Exploration`

Archived here:

- legacy autonomous proof-discovery scripts from the old `skynet` path
- archived declaration-graph wrapper now served through `tools/graph.py` as a compatibility shim
- scratch Lean files removed from the package build surface

Practical rule:

- mine this directory for ideas or historical context;
- do not route new automation through it unless you are intentionally reviving
  an old line of work.
