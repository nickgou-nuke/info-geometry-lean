# Codebase Status

> Status: `verified active surface`
> Audited: 2026-07-24
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/REPOSITORY_BOUNDARY_POLICY.md](REPOSITORY_BOUNDARY_POLICY.md)

This file is the maintained prose status snapshot for the repository.

Last refreshed: 2026-07-24 (Europe/Sofia)

## Verified Scope Of This Refresh

This documentation repair audited the current repository structure against:

- `lakefile.lean`
- `lean/`
- `src/igf/`
- `tools/`

This refresh specifically validates a **fresh full build** of the codebase.

## Observed Live Surface

Lean:

- package: `infogeometry`
- entry file: `lean/InfoGeometry.lean`
- full umbrella: `lean/InfoGeometry/All.lean`
- canonical audit/architecture anchors:
  - `lean/InfoGeometry/Audit.lean`
  - `lean/InfoGeometry/Meta/`

## Working Tree Reality

At the time of the audit (2026-07-24), the working tree is clean concerning build constraints, with the active open debt reduced to exactly 5 compiler-visible gaps.

Observed active edits included:
- Refactoring the 8 generated files in `Automath/Generated/` to import `CuntzFibonacciFiveHypotheses.lean` and construct real mathematical bridge proofs, eliminating the vacuous addition/multiplication stubs.
- Verification of 100% build compatibility of the `Automath` module.
- Retaining 5 honest, compiler-tracked open gaps (1 in `GenuineBounds.lean`, 1 in `Pin55KreinConformalBridge.lean`, and 3 in the `GoldenMeanShift.lean` sandbox) rather than masking them using typeclass wrappers, upholding the UTMOST MANDATE and the Goutev Principle of Epistemic Rigor.

## Documentation Truth Model

Current authority order:

1. `lean/` and `lakefile.lean` (The absolute truth layer, fully compiled as of 2026-07-09)
2. `src/igf/` and maintained scripts under `tools/`
3. this file
4. maintained entry docs listed in [README.md](../README.md) and [docs/README.md](README.md)
5. generated reports and reference-memory notes

## Markdown Corpus Result

The repository contains a large Markdown corpus, but most of it is not current
authority.

After the 2026-07-09 build cleanup:

- canonical docs were aligned around the currently compiling code surface.
- `docs/black_books/` remains untouched by design.

## Current Risks

- Historical handover and archive docs remain useful for provenance, but should
  not drive current edits, as many reflect pre-compilation states.
- The environment is currently stable and locked in, so future edits must preserve the `InfoGeometry.All` build matrix.

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
