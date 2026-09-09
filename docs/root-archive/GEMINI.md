# Gemini Use Policy

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for optional ideation workflow, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This file describes how Gemini-style ideation fits into the current repository
workflow.

## Current Role

Gemini-like exploration is optional and proposal-only.

It may help with:

- brainstorming candidate bridges
- external literature distillation
- packet enrichment before formal implementation

It does not decide theorem truth, module ownership, or closure status.

## Boundary

If a Gemini-generated idea matters, it must be translated into:

- a current owner file
- a concrete Lean or tooling change
- a current verification step

Without that translation, it stays exploratory.

## Authority Order

1. current code in `lean/`, `src/igf/`, and maintained `tools/`
2. current repo-level docs
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
