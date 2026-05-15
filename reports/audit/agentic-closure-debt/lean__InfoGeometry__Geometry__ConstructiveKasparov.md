# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:36.658127+00:00`
Root: `lean/InfoGeometry/Geometry/ConstructiveKasparov.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **42**
- Hard: **0**
- Soft: **25**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/ConstructiveKasparov.lean` | `advisory` | 67 | 0 | 25 | 17 | 42 |

## Findings by file

### `lean/InfoGeometry/Geometry/ConstructiveKasparov.lean`
- module: `InfoGeometry.Geometry.ConstructiveKasparov`
- status: `advisory`
- debt_score: `67`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field VerifiedBoundedDirac.F_sq_add_P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field VerifiedBoundedDirac.F_P_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field VerifiedBoundedDirac.P_F_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field VerifiedBoundedDirac.P_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [advisory] `local-hypothesis-injection` in `theorem F_cube_eq_F` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L63 [soft] `law-field-locker` in `structure-field KasparovIndexDatum.superReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field KasparovIndexDatum.super_sub` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [advisory] `local-hypothesis-injection` in `theorem mckean_singer_is_kasparov_defect` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L112 [soft] `law-field-locker` in `structure-field FiniteGradedKernelDatum.kernelBasis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field FiniteGradedKernelDatum.grade` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L166 [soft] `skeletal-proof` in `theorem kernelIndex_eq_even_count_sub_odd_count` — proof appears to close via minimal tactic one-liner
  - L176 [soft] `skeletal-proof` in `theorem kernelIndex_eq_zero_of_kernelBasis_eq_nil` — proof appears to close via minimal tactic one-liner
  - L185 [advisory] `existential-packaging` in `theorem exists_mode_of_kernelIndex_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L213 [soft] `law-field-locker` in `structure-field ConstructiveKasparovDatum.F` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L215 [soft] `law-field-locker` in `structure-field ConstructiveKasparovDatum.defectToKernelProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field ConstructiveKasparovDatum.kernelBasisOfProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field ConstructiveKasparovDatum.grade` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L237 [soft] `skeletal-proof` in `theorem defect_eq_one_sub_square` — proof appears to close via minimal tactic one-liner
  - L252 [soft] `skeletal-proof` in `theorem Pker_eq_defect_readout` — proof appears to close via minimal tactic one-liner
  - L283 [soft] `skeletal-proof` in `theorem index_eq_projected_kernel_index` — proof appears to close via minimal tactic one-liner
  - L292 [soft] `skeletal-proof` in `theorem index_eq_zero_of_projected_kernel_empty` — proof appears to close via minimal tactic one-liner
  - L303 [advisory] `existential-packaging` in `theorem exists_projected_kernel_mode_of_index_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L330 [soft] `law-field-locker` in `structure-field ExactDefectStokesBridge.defectDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L332 [soft] `law-field-locker` in `structure-field ExactDefectStokesBridge.geometricDerivative_eq_defectDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L397 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L475 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L510 [advisory] `local-hypothesis-injection` in `theorem boundaryIntegral_ne_zero_iff_finiteKernelIndex_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L517 [advisory] `local-hypothesis-injection` in `theorem boundaryIntegral_ne_zero_iff_finiteKernelIndex_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L571 [soft] `law-field-locker` in `structure-field ConstructiveKasparovFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L574 [soft] `law-field-locker` in `structure-field ConstructiveKasparovFlow.flat_index_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L580 [soft] `law-field-locker` in `structure-field ConstructiveKasparovFlow.flow_preserves_index` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L591 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L603 [advisory] `local-hypothesis-injection` in `theorem nonzero_index_cannot_flow_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L606 [advisory] `local-hypothesis-injection` in `theorem nonzero_index_cannot_flow_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L631 [soft] `law-field-locker` in `structure-field ConstructiveResidueReadout.regionOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L633 [soft] `law-field-locker` in `structure-field ConstructiveResidueReadout.index_eq_winding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L650 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L665 [advisory] `local-hypothesis-injection` in `theorem nonzero_boundaryIntegral_cannot_flow_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

