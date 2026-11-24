<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](../docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# Tooling Overview

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

This directory contains the maintained script surface around the Lean codebase.

## Current Maintained Lanes

- `tools/infra/`
  build orchestration, DAG refresh/reporting, audits, packet workflows
- `tools/frontier/`
  proof-session and semantic/frontier helpers
- `tools/docs/`
  documentation refresh helpers
- `tools/observability/`
  static Lean graph overlay, wrapper dedup, auto-tagging, and audit reports
  - compatibility wrapper: `tools/observability/lean_graph_overlay.py`
- `tools/leantrail/`
  LeanTrail conformance, export, ingest, and path/failure tooling
- `tools/alexandria/`
  external-corpus ingest and GraphRAG retrieval (BM25 + PageRank navigation);
  see [docs/DAGToolchainAndAlexandriaTrace.md](../docs/DAGToolchainAndAlexandriaTrace.md)

There is also a real Python package under `src/igf/` that now owns a growing
part of the artifact pipeline and CLI surface.

## Live Entrypoints

Lake-managed commands from `lakefile.lean`:

- `lake script run changedVerify`
- `lake script run dagStatus`
- `lake script run dagRefresh`
- `lake script run dagReports`
- `lake script run dagDoctor`
- `lake script run dagAll`
- `lake script run leantrailConformance`
- `lake script run leantrailExport`
- `lake script run leantrailArangoIngest`
- `lake script run leantrailArangoPhysicsEval`
- `lake script run leantrailFailureHarvest`
- `lake script run leantrailPathLock`
- `lake script run leantrailHolePackets`

Python CLIs:

- `igf`
- `infogeometry`

Alexandria GraphRAG smoke checks (repo venv has `networkx` and `python-arango`):

```bash
.venv/bin/python3 tools/alexandria/retrieve_context.py \
  --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
  --query "Krein space fundamental symmetry Peirce decomposition" \
  --top-k 5 --hops 2 --format text
```

```bash
.venv/bin/python3 tools/alexandria/graph_context_rank.py \
  --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
  --query "Drazin inverse Riesz projector spectral decomposition" \
  --top-k 5 --hops 2 --format text
```

These are `retrieval_context_only` navigation results, not Lean proof evidence.
The default Alexandria target is `:8532` / `alexandria`; `:8530` and `:8540`
are forbidden by `guard_alexandria_target`. See
[docs/DAGToolchainAndAlexandriaTrace.md](../docs/DAGToolchainAndAlexandriaTrace.md).

## Wrapper Rule

Many top-level `tools/*.py` files are compatibility wrappers or convenience
entrypoints. When changing behavior, prefer editing the maintained module under
its owning subdirectory or under `src/igf/`.

## Start Here

- [infra/README.md](infra/README.md)
- [docs/README.md](docs/README.md)
- [../docs/OperatorQuickstart.md](../docs/OperatorQuickstart.md)
- [../docs/DAGTroubleshooting.md](../docs/DAGTroubleshooting.md)
- [../leantrail/README.md](../leantrail/README.md)
