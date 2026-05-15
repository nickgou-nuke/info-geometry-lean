# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.577720+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **72**
- Hard: **0**
- Soft: **34**
- Advisory: **38**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean` | `advisory` | 106 | 0 | 34 | 38 | 72 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean`
- module: `InfoGeometry.Canonical.DrazinInfiniteCore`
- status: `advisory`
- debt_score: `106`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [advisory] `local-hypothesis-injection` in `theorem descentAtZero_of_isDrazinInverse_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [soft] `skeletal-proof` in `theorem ascentAtZero_of_isDrazinInverse_le` — proof appears to close via minimal tactic one-liner
  - L80 [advisory] `local-hypothesis-injection` in `theorem ascentAtZero_of_isDrazinInverse_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [advisory] `local-hypothesis-injection` in `theorem ascentAtZero_of_isDrazinInverse_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L91 [advisory] `local-hypothesis-injection` in `theorem ascentAtZero_of_isDrazinInverse_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [advisory] `local-hypothesis-injection` in `theorem ascentAtZero_of_isDrazinInverse_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `local-hypothesis-injection` in `theorem ascentAtZero_of_isDrazinInverse_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_finiteAscentDescent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L148 [advisory] `bridge-shaped-declaration` in `theorem exists_drazinInverse_of_finiteAscentDescent_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L148 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_finiteAscentDescent_readback` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L158 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_fitting` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L158 [soft] `skeletal-proof` in `theorem exists_drazinInverse_of_fitting` — proof appears to close via minimal tactic one-liner
  - L168 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L197 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L201 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L210 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L213 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L228 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L231 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L251 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L254 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L256 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L272 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L287 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L296 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L304 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L307 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L313 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L319 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L322 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_of_fitting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L337 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_finiteAscentDescent_constructive` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L358 [advisory] `existential-packaging` in `def ZeroIsolatedInSpectrum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L367 [soft] `law-field-locker` in `structure-field HasClassicalRieszDecompositionAtZero.P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L368 [soft] `law-field-locker` in `structure-field HasClassicalRieszDecompositionAtZero.P_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field HasClassicalRieszDecompositionAtZero.PT_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L371 [soft] `law-field-locker` in `structure-field HasClassicalRieszDecompositionAtZero.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L373 [soft] `law-field-locker` in `structure-field HasClassicalRieszDecompositionAtZero.hP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L384 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.P_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L385 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.PT_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L386 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.S` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L387 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.left_inverse_on_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L389 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.right_inverse_on_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L391 [soft] `law-field-locker` in `structure-field HasGeneralizedRieszDecompositionAtZero.quasinilpotent_on_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L402 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L403 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.P_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.PT_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L405 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.S` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L406 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.left_inverse_on_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L407 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.right_inverse_on_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L408 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.S_supported_on_regular_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L409 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.S_supported_on_regular_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L410 [soft] `law-field-locker` in `structure-field ConstructiveRieszDecompositionAtZero.nilpotent_on_complement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L422 [soft] `skeletal-proof` in `theorem constructiveDrazinCandidate_comm` — proof appears to close via minimal tactic one-liner
  - L434 [soft] `skeletal-proof` in `theorem constructiveDrazinCandidate_inner` — proof appears to close via minimal tactic one-liner
  - L449 [soft] `skeletal-proof` in `theorem constructiveDrazinCandidate_power` — proof appears to close via minimal tactic one-liner
  - L467 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_constructiveRieszDecompositionAtZero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L530 [soft] `law-field-locker` in `structure-field DrazinInfiniteAssumptions.finite_ascent_descent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L531 [soft] `law-field-locker` in `structure-field DrazinInfiniteAssumptions.zero_isolated_spectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L532 [soft] `law-field-locker` in `structure-field DrazinInfiniteAssumptions.classical_riesz` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L533 [soft] `law-field-locker` in `structure-field DrazinInfiniteAssumptions.generalized_riesz` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L549 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_rieszDecomposition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L573 [soft] `law-field-locker` in `structure-field RieszDrazinData.hP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L635 [advisory] `existential-packaging` in `theorem nonempty_rieszDrazinData_endCLM` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L635 [soft] `skeletal-proof` in `theorem nonempty_rieszDrazinData_endCLM` — proof appears to close via minimal tactic one-liner
  - L646 [soft] `classical-witness-smuggling` in `def canonicalRieszDrazinData_endCLM` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L661 [soft] `skeletal-proof` in `theorem canonicalDrazinInverse_endCLM_spec` — proof appears to close via minimal tactic one-liner

