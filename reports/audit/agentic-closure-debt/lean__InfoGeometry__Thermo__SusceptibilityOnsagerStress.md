# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.691763+00:00`
Root: `lean/InfoGeometry/Thermo/SusceptibilityOnsagerStress.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **16**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/SusceptibilityOnsagerStress.lean` | `advisory` | 40 | 0 | 16 | 8 | 24 |

## Findings by file

### `lean/InfoGeometry/Thermo/SusceptibilityOnsagerStress.lean`
- module: `InfoGeometry.Thermo.SusceptibilityOnsagerStress`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `law-field-locker` in `structure-field OnsagerTwoOperatorForm.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field OnsagerTwoOperatorForm.diagonal_nonnegative_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L105 [soft] `law-field-locker` in `structure-field SusceptibilityOnsagerPairing.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field SusceptibilityOnsagerPairing.pairing_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field SusceptibilityOnsagerPairing.pairing_from_susceptibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L157 [soft] `law-field-locker` in `structure-field StressTensorOperator.stress` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field StressTensorOperator.stress_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field StressTensorOperator.constitutive_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `law-field-locker` in `structure-field ThermodynamicOperatorDerivation.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field ThermodynamicOperatorDerivation.map_add_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [soft] `law-field-locker` in `structure-field ThermodynamicOperatorDerivation.map_smul_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field ThermodynamicOperatorDerivation.leibniz_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field ThermodynamicOperatorDerivation.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L274 [soft] `law-field-locker` in `structure-field DerivedStressTensorResponse.derivedStress` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [soft] `law-field-locker` in `structure-field DerivedStressTensorResponse.derivedStress_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L353 [soft] `law-field-locker` in `structure-field SusceptibilityOnsagerStressPacket.onsager_controls_stress_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L427 [advisory] `existential-packaging` in `def SusceptibilityOnsagerStressOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

