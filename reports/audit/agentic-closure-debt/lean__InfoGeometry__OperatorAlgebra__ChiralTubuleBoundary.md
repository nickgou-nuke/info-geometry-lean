# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:07.448083+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ChiralTubuleBoundary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **19**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ChiralTubuleBoundary.lean` | `advisory` | 54 | 0 | 19 | 16 | 35 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ChiralTubuleBoundary.lean`
- module: `InfoGeometry.OperatorAlgebra.ChiralTubuleBoundary`
- status: `advisory`
- debt_score: `54`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `law-field-locker` in `structure-field HessianCollapseEvent.hessian_collapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field HessianCollapseEvent.rank_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field ShearReadout.shear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field ExtremeShearThreshold.threshold_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L123 [soft] `law-field-locker` in `structure-field UnruhShearCalibration.temperature_crosses_threshold` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field UnruhShearCalibration.temperature_drives_shear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L165 [soft] `law-field-locker` in `structure-field TopologicalObstruction.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `law-field-locker` in `structure-field TopologicalObstruction.flat_invariant_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field TopologicalObstruction.nontrivial_at` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L206 [soft] `law-field-locker` in `structure-field ChiralResidue.chiral_residue_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field ChiralResidue.stable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L253 [soft] `law-field-locker` in `structure-field ChiralTubuleBoundaryWitness.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L266 [soft] `law-field-locker` in `structure-field ChiralTubuleBoundaryWitness.residue_at_collapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [advisory] `existential-packaging` in `theorem exists_stable_chiral_residue` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L334 [soft] `law-field-locker` in `structure-field UnruhDrivenChiralTubuleBoundary.driven_eq_collapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L338 [soft] `law-field-locker` in `structure-field UnruhDrivenChiralTubuleBoundary.threshold_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L370 [advisory] `existential-packaging` in `theorem exists_stable_chiral_residue` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L409 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L421 [advisory] `existential-packaging` in `theorem no_nontrivial_flattening` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L443 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L485 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L555 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L564 [advisory] `existential-packaging` in `theorem locally_lost_has_chiral_lightcone_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L572 [advisory] `existential-packaging` in `theorem locally_lost_is_commutant_chiral_lightcone` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L603 [soft] `law-field-locker` in `structure-field JonesRankCollapseEvent.p_channel_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L607 [soft] `law-field-locker` in `structure-field JonesRankCollapseEvent.s_channel_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L614 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L621 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L647 [advisory] `existential-packaging` in `def ChiralTubuleBoundaryOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L647 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L671 [advisory] `existential-packaging` in `def UnruhDrivenChiralTubuleOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

