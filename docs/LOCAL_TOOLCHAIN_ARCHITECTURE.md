# Local Toolchain Architecture

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current local topology map, but subordinate to current code and status docs.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document is the short topology map for the current local toolchain.

## Authority Layer

Truth lives in:

- `lean/`
- `lakefile.lean`

Everything else is support infrastructure around that code.

## Main Local Layers

1. Lean build and verification
   - `lake env lean`
   - `lake build`
   - `lake script run changedVerify`
2. DAG and report management
   - `lake script run dagStatus`
   - `lake script run dagDoctor`
   - `lake script run dagAll`
3. Frontier inspection
   - `lake script run proofSession`
   - `lake script run proofPrint`
   - `lake script run semanticSnapshot`
4. LeanTrail carrier tools
   - `lake script run leantrailConformance`
   - `lake script run leantrailExport`
   - `lake script run leantrailArangoIngest`

## Local Rule

Use the narrowest layer that answers the question.

- changed code: use Lean file/module checks and `changedVerify`
- stale structural view: use `dagDoctor`
- full repository artifact refresh: use `dagAll`
- graph-carrier comparison: use LeanTrail commands

## Artifact Rule

`reports/` and `artifacts/` are local support surfaces. They are useful, but
they are not the authority layer.
