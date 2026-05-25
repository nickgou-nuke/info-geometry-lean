# Codebase Status

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md), [docs/REPOSITORY_BOUNDARY_POLICY.md](REPOSITORY_BOUNDARY_POLICY.md)

This file is stale as an authority source. Treat it as a snapshot only and
re-audit against the live repository before using it to guide edits.

Last refreshed: 2026-05-02 (Europe/Sofia)

This file is the maintained prose status snapshot for the repository.

## Verified Scope Of This Refresh

This documentation repair audited the current repository structure against:

- `lakefile.lean`
- `pyproject.toml`
- `lean/`
- `src/igf/`
- `tools/`
- tracked Markdown layout under `docs/`, `reports/`, `archive/`, and `handover/`

It did not claim a fresh full build or full DAG regeneration.

## Observed Live Surface

Lean:

- package: `infogeometry`
- entry file: `lean/InfoGeometry.lean`
- full umbrella: `lean/InfoGeometry/All.lean`
- canonical audit/architecture anchors:
  - `lean/InfoGeometry/Audit.lean`
  - `lean/InfoGeometry/Meta/`

Python:

- package metadata in `pyproject.toml`
- console scripts:
  - `igf = igf.cli:main`
  - `infogeometry = scripts.cli:main`
- maintained package under `src/igf/` with:
  - `config/`
  - `artifacts/`
  - `graph/`
  - `pipeline/`
  - `policy/`

Lake-script operator surface present in `lakefile.lean`:

- `strictCheck`
- `semanticAudit`
- `semanticSnapshot`
- `proofSession`
- `proofPrint`
- `dagStatus`
- `dagRefresh`
- `dagReports`
- `dagDoctor`
- `dagAll`
- `changedVerify`
- LeanTrail scripts for conformance/export/Arango/failure/path-lock/hole-packets

## Working Tree Reality

At the time of the audit, the working tree was dirty.

Observed active edits included:

- many tracked Lean files under `lean/InfoGeometry/...`
- tracked Python changes under `src/igf/`
- new arithmetic and thermodynamics Lean modules
- new IGF CLI tests and `tools/igf.py`
- new Black Book files under `docs/black_books/`

This doc refresh did not overwrite those code changes.

## Documentation Truth Model

Current authority order:

1. `lean/` and `lakefile.lean`
2. `src/igf/` and maintained scripts under `tools/`
3. this file
4. maintained entry docs listed in [README.md](../README.md) and [README.md](README.md)
5. generated reports and reference-memory notes

## Markdown Corpus Result

The repository contains a large Markdown corpus, but most of it is not current
authority.

After the 2026-05-02 cleanup:

- canonical docs were rewritten around the current code surface
- generated and historical Markdown was explicitly labeled
- `docs/black_books/` was left untouched by design

## Current Risks

- Many checked-in `reports/*.md` and `reports/dag/*.md` files are snapshots, not
  live state
- Historical handover and archive docs remain useful for provenance, but should
  not drive current edits
- A dirty worktree means any status claim beyond structure must be treated
  carefully until targeted verification is rerun

## Next Verification Commands

If you need fresh runtime truth, run:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

If you need a full artifact refresh:

```bash
lake script run dagAll
```

## UTMOST MANDATE: Native Lean proof closure over witness/certificate temporary scaffolding (Native Closure Mandated: Closure Debt)

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate field (Native Closure Mandated: Closure Debt)s, external certificates, and assumption interfaces are temporary temporary scaffolding (Native Closure Mandated: Closure Debt) only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
