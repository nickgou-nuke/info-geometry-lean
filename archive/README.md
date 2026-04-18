# Archive

> Status: historical/reference subtree; not authoritative for active build policy.
> Canonical entry docs: [`README.md`](../README.md), [`docs/README.md`](../docs/README.md).
> Markdown governance: [`docs/MarkdownCorpusGovernance.md`](../docs/MarkdownCorpusGovernance.md).

This directory contains historical material intentionally kept inside the
repository for provenance, design archaeology, and idea recovery.

Use this rule:

- start in the active repository surface first;
- enter `archive/` only when you are explicitly researching past approaches,
  discarded experiments, or old automation ideas.

## Status Model

Archived material is not part of the supported build or automation surface.
It may still contain:

- useful design ideas,
- historical proof-search experiments,
- scratch derivations worth revisiting,
- earlier versions of workflows later replaced by cleaner infrastructure.

It should not be treated as authoritative over the current stack.

## Current Authoritative Surface

For current work, prefer:

- `lean/InfoGeometry/`
- `lean/DAG/`
- `lean/scripts/DAG/Exploration/`
- `tools/semantic_block_export.py`
- `tools/skynet_v2.py`
- `tools/update_repo_docs.py`

## Archive Layout

- `archive/legacy/`
  The first historical bucket. It currently holds:
  - old autonomous-proof-discovery Python scripts,
  - scratch Lean files removed from the package build surface.

See [archive/legacy/README.md](/home/goutev/LEAN4/info-geometry-lean/archive/legacy/README.md) for the local notes on that bucket.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md) for the current build/audit state.
