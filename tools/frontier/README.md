# Frontier Tools

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

This directory contains the maintained frontier and proof-inspection helpers.

## Main Entrypoints

- `semantic_block_export.py`
- `semantic_snapshot.py`
- `proof_session.py`
- `proof_print.py`
- `skynet_v2.py`
- `extract_module_patch.py`

## Role

Use this lane when you need:

- semantic export of a specific Lean file or module
- proof-state or declaration-value inspection
- a targeted frontier packet around a seed declaration

Do not use this lane as proof authority. It is an exploration and inspection
surface around the actual Lean code.

## Preferred Commands

```bash
lake script run proofSession
lake script run proofPrint -- <Decl.Name>
lake script run semanticSnapshot
```

For repo-wide structure or stale report repair, go back to the DAG lane under
`tools/infra/`.
