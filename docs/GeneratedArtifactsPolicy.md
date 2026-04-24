# Generated Artifacts Policy

This repository separates **canonical source** from **generated artifacts**.

## Canonical Source

The following trees are canonical and are expected to stay in normal Git:

- `lean/`
- `docs/`
- `tests/`
- `tools/`
- small hand-maintained policy/manifests that act as source-of-record

When documentation and Lean disagree, Lean is the authority.

## Generated Artifact Families

The following families are generated outputs and should not be treated as
canonical inputs:

- `artifacts/alexandria/`
  - semantic ingest corpora
  - retrieval overlays
  - research digests
- `artifacts/infotree/`
  - raw InfoTree exports
  - Arango hydration/overlay exports
  - perf and probe payloads
- `artifacts/leantrail/`
  - trail snapshots
  - conformance and failure-harvest reports
- `artifacts/expr-graph/`
  - expression-graph exports
- `artifacts/hermes_loop/`
  - queue, replay, worker, and runtime loop outputs
- `artifacts/socratic_loops/`
  - generated loop transcripts and eval outputs
- `artifacts/black_book_alchemy/`
  - generated synthesis byproducts
- `handover/injections/manifests/EXT-*`
  - generated extension manifests

These paths are intentionally ignored going forward and should be reproducible
from the repo toolchain.

## Regeneration Principle

If a generated artifact is needed again, regenerate it from the owning source
and tool, rather than restoring it by hand.

Typical owners:

- declaration/DAG refresh:
  - `lake script run dagRefresh`
  - `python3 tools/infra/refresh_decl_graph.py`
- Arango overlays:
  - `python3 tools/infra/arango_layered_ingest.py`
  - `python3 tools/infra/arango_dag_algorithms.py`
- Alexandria ingest/fetch:
  - `tools/alexandria/*`
- Hermes/hive runtime outputs:
  - `tools/infra/hive_*`
  - `tools/infra/research_digest_worker.py`

## Practical Rule

Before committing an artifact-like path, ask:

1. Is this a source input, or only a generated result?
2. If deleted, can it be recreated from tracked source and tooling?
3. Is the repo depending on it as a de facto canonical input?

If it is generated, reproducible, and non-canonical, it should stay out of Git.
