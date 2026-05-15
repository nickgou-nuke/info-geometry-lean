# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:35.893283+00:00`
Root: `lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **78**
- Hard: **0**
- Soft: **69**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean` | `advisory` | 147 | 0 | 69 | 9 | 78 |

## Findings by file

### `lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean`
- module: `InfoGeometry.Geometry.BilingualPoincareMetric`
- status: `advisory`
- debt_score: `147`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L71 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L157 [soft] `simp-law-injection` in `simp-declaration imaginaryQuadratic_eq_kHeightQuadratic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L160 [soft] `skeletal-proof` in `theorem imaginaryQuadratic_eq_kHeightQuadratic` — proof appears to close via minimal tactic one-liner
  - L214 [soft] `law-field-locker` in `structure-field ImaginaryRiesz.form_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field ImaginaryRiesz.positive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field ImaginaryRiesz.unit_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [soft] `law-field-locker` in `structure-field TraceDatum.tr` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field TraceDatum.cyclic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [soft] `law-field-locker` in `structure-field MobiusDenominatorInverse.denom_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field MobiusDenominatorInverse.inv_denom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L408 [soft] `simp-law-injection` in `simp-declaration zero_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L410 [soft] `skeletal-proof` in `theorem zero_op` — proof appears to close via minimal tactic one-liner
  - L425 [soft] `simp-law-injection` in `simp-declaration add_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L427 [soft] `skeletal-proof` in `theorem add_op` — proof appears to close via minimal tactic one-liner
  - L442 [soft] `simp-law-injection` in `simp-declaration neg_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L444 [soft] `skeletal-proof` in `theorem neg_op` — proof appears to close via minimal tactic one-liner
  - L459 [soft] `simp-law-injection` in `simp-declaration sub_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L461 [soft] `skeletal-proof` in `theorem sub_op` — proof appears to close via minimal tactic one-liner
  - L477 [soft] `simp-law-injection` in `simp-declaration smul_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L479 [soft] `skeletal-proof` in `theorem smul_op` — proof appears to close via minimal tactic one-liner
  - L521 [soft] `simp-law-injection` in `simp-declaration moebiusTangentPushForward_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L523 [soft] `skeletal-proof` in `theorem moebiusTangentPushForward_op` — proof appears to close via minimal tactic one-liner
  - L533 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L564 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.innerAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L568 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L573 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.add_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L579 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.smul_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L585 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.positive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L590 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.definite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L595 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.moebius_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L615 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L703 [soft] `simp-law-injection` in `simp-declaration operatorCommutator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L734 [soft] `simp-law-injection` in `simp-declaration commutator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L736 [soft] `skeletal-proof` in `theorem commutator_self` — proof appears to close via minimal tactic one-liner
  - L741 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L772 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L791 [soft] `law-field-locker` in `structure-field BilingualPoincareMetricAdmissible.K_square_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L799 [advisory] `existential-packaging` in `def BilingualPoincareMetricOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L827 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L829 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L833 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L886 [advisory] `existential-packaging` in `def SameProjectiveRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L926 [soft] `skeletal-proof` in `theorem height_pos` — proof appears to close via minimal tactic one-liner
  - L961 [soft] `law-field-locker` in `structure-field TangentAt.zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L974 [soft] `simp-law-injection` in `simp-declaration zero_vel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L976 [soft] `skeletal-proof` in `theorem zero_vel` — proof appears to close via minimal tactic one-liner
  - L979 [soft] `simp-law-injection` in `simp-declaration add_vel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L981 [soft] `skeletal-proof` in `theorem add_vel` — proof appears to close via minimal tactic one-liner
  - L985 [soft] `simp-law-injection` in `simp-declaration neg_vel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L987 [soft] `skeletal-proof` in `theorem neg_vel` — proof appears to close via minimal tactic one-liner
  - L991 [soft] `simp-law-injection` in `simp-declaration sub_vel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L993 [soft] `skeletal-proof` in `theorem sub_vel` — proof appears to close via minimal tactic one-liner
  - L997 [soft] `simp-law-injection` in `simp-declaration smul_vel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L999 [soft] `skeletal-proof` in `theorem smul_vel` — proof appears to close via minimal tactic one-liner
  - L1018 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.innerAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1022 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1028 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.add_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1035 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.smul_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1043 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1049 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.definite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1055 [soft] `law-field-locker` in `structure-field PoincareMetricDatum.boundary_absolute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1070 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1144 [soft] `law-field-locker` in `structure-field BilingualAutomorphism.map` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1148 [soft] `law-field-locker` in `structure-field BilingualAutomorphism.pushTangent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1153 [soft] `law-field-locker` in `structure-field BilingualAutomorphism.automorphism_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1183 [soft] `law-field-locker` in `structure-field BilingualMobiusSymmetry.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1213 [soft] `law-field-locker` in `structure-field PoincareMetricSpectralBackend.tangentOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1217 [soft] `law-field-locker` in `structure-field PoincareMetricSpectralBackend.spectralPairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1221 [soft] `law-field-locker` in `structure-field PoincareMetricSpectralBackend.metric_eq_spectralPairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1228 [soft] `law-field-locker` in `structure-field PoincareMetricSpectralBackend.backend_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1232 [advisory] `existential-packaging` in `structure PoincareMetricAdmissible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1244 [soft] `law-field-locker` in `structure-field PoincareMetricAdmissible.positiveCone_nonempty` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1247 [soft] `law-field-locker` in `structure-field PoincareMetricAdmissible.isotropicCone_is_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1251 [soft] `law-field-locker` in `structure-field PoincareMetricAdmissible.metric_construction_available` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1255 [advisory] `existential-packaging` in `def BilingualPoincareMetricOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

