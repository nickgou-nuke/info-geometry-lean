# Frontier Protocol

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this workflow, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

Frontier work in this repository means generating candidate directions, not
claiming proof.

## Frontier Output Standard

A good frontier packet:

- names real current files or declarations
- starts from current code, not mythology
- isolates one testable next move
- can be checked by local build, semantic export, or targeted inspection

## Current Tools

Use the maintained frontier lane:

- `lake script run proofSession`
- `lake script run proofPrint`
- `lake script run semanticSnapshot`
- `tools/frontier/semantic_block_export.py`
- `tools/frontier/skynet_v2.py`

## Boundary

Frontier artifacts may suggest:

- a missing bridge
- an owner split
- a smaller theorem statement
- a proof corridor worth testing

They do not establish theorem truth. Lean does.

## Practical Rule

If a frontier note cannot be reduced to a concrete owner file and a concrete
verification step, it stays exploratory.
