# Dahm–Klein verification status

## Draft checkpoint — verification pending

This is a fresh reconstruction on base
`c143c264bc18bbf41d692be4e270b5b7f7405702`. The user requested an upstream
draft PR on 2026-11-11 to preserve the work while the local build continues.
The earlier lost checkout and its acceptance records are not evidence for
this source. No independent acceptance receipt is claimed or included yet.

## Observed checks at publication

- Independent non-authoring source review: **PASS**, including the theorem
  contract, all five mathematical owners, audit, focused configuration, and CI.
- Pinned Lean: `leanprover/lean4:v4.34.1`.
- Pinned Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Mathlib cache retrieval completed successfully for 8,908 files.
- The first focused build is still running. It has successfully compiled
  `ExteriorKleinOperatorAction` and `ExteriorKleinOperatorExamples`.
- Determinant covariance, boosts, incidence transport, and the declaration
  audit have not yet completed compilation in this checkout.
- The source contains 37 named mathematical theorems; this source count is
  not a claim that all 37 have passed Lean or the axiom audit.
- Fresh declaration/axiom audit, independent QA acceptance, and the remaining
  source gates are pending. No generated-declaration totals are asserted.

The action and example build results are progress evidence only. Overall
focused acceptance remains pending until the complete build, fresh audit,
source gates, and independent checks succeed against the final source.

## Root integration boundary

The root package requires local external repositories. In this checkout,
`external_refs/homotopy-hypothesis-lean4` and `external_refs/atlas-lean` are
absent, and `external_refs/gift-framework-core` is an uninitialized submodule.
The root target check is queued behind the shared build lock; a fresh root
build or pre-push success is not claimed. Root configuration, dependency pins,
existing mathematical owners, and tracked hooks are unchanged.

## Reproduction and next checks

Use the commands in [README.md](README.md). The focused build and fresh audit
use the shared lock. The included GitHub Actions workflow will perform its own
build, fresh audit, and strict source screen after the PR is opened; hosted
execution is not yet observed at this checkpoint.

This document will be updated with actual diagnostics or an independent,
checksummed acceptance receipt as verification finishes. The PR remains a
draft and does not request a merge.
