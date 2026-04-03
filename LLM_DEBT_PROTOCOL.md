# LLM Debt Protocol

Debt work in this repository means replacing wrappers, assumptions, surrogates, or stale interfaces with real lower-owner mathematics.

## Role split

- creative lane: propose replacement lemmas, owner splits, and local constructive proofs;
- critical lane: reject cosmetic rewrites, API noise, and wrapper-preserving edits;
- Lean lane: decide what is true.

## Current debt discipline

Treat as debt:
- public packaging wrappers;
- fake capstone surfaces;
- stale umbrella ownership;
- surrogate or vacuous theorem surfaces;
- duplicated presentation layers over one lower trunk.

Do not treat as debt:
- genuine lower bridge identifications;
- actual constructive endpoints;
- stable substrate definitions.

## Current tooling

Use:
- `scripts/quality/audit_constructivity.py`
- `tools/infra/generate_theorem_surface_index.py`
- `tools/infra/generate_semantic_quotient.py`
- `tools/infra/generate_projection_coloring.py`
- `tools/infra/refresh_decl_graph.py` (incremental DAG refresh; use `--force` to bypass olean-hash skip)
- `artifacts/dag/index/meta.json` — verify freshness (`schemaVersion` ≥ 2, recent `timestamp`) before trusting any derived report

Always do direct file analysis first.
Check `meta.json` before relying on any DAG artifact for debt triage.
