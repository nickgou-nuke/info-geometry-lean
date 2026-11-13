# Verification record: tripotent compression

## Scope and source base

- Base commit: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- The focused package checks the canonical repository sources without copying,
  rewriting, stubbing, or replacing their imports.
- Root dependency specifications and all publication gates are unchanged.

## Independent review and static checks

- A-A semantic review: PASS, including the arbitrary real-Hilbert common-kernel
  criterion and its distinction from uniform coercivity.
- QA-A independent source review: STATIC PASS; all nine local dependency
  checkouts match the resolved root/focused revisions.
- Staged proof proxy gate: exit 0.
- Vacuity linter on the six touched mathematical modules: no findings.
- Placeholder/custom-axiom/unsafe/partial scans: no findings.
- Staged whitespace check: exit 0.

## Kernel and integration checks

The serialized compiler runs are pending. No Lean compilation, declaration-
axiom audit, full-project success, or publication acceptance is claimed by this
interim record. Replace this section with actual results before delivery.
