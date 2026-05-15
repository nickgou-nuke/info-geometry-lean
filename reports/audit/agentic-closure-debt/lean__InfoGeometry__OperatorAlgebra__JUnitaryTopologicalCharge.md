# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:16.308127+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **42**
- Hard: **0**
- Soft: **28**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean` | `advisory` | 70 | 0 | 28 | 14 | 42 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean`
- module: `InfoGeometry.OperatorAlgebra.JUnitaryTopologicalCharge`
- status: `advisory`
- debt_score: `70`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `law-field-locker` in `structure-field AdjointDatum.adj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field DeterminantDatum.det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field DeterminantDatum.det_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field DeterminantDatum.det_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field AdjointDeterminantDatum.det_adj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L82 [soft] `simp-law-injection` in `simp-declaration det_one_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `skeletal-proof` in `theorem det_sq_eq_one` — proof appears to close via minimal tactic one-liner
  - L150 [advisory] `local-hypothesis-injection` in `theorem det_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L168 [advisory] `local-hypothesis-injection` in `theorem det_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L172 [advisory] `local-hypothesis-injection` in `theorem det_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L180 [advisory] `local-hypothesis-injection` in `theorem det_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `theorem det_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [soft] `simp-law-injection` in `simp-declaration determinantCharge_eq_one_of_det_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L236 [soft] `skeletal-proof` in `theorem determinantCharge_eq_one_of_det_pos` — proof appears to close via minimal tactic one-liner
  - L242 [soft] `simp-law-injection` in `simp-declaration determinantCharge_eq_neg_one_of_det_nonpos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L244 [soft] `skeletal-proof` in `theorem determinantCharge_eq_neg_one_of_det_nonpos` — proof appears to close via minimal tactic one-liner
  - L250 [soft] `simp-law-injection` in `simp-declaration determinantZ2Charge_eq_positive_of_det_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `skeletal-proof` in `theorem determinantZ2Charge_eq_positive_of_det_pos` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `simp-law-injection` in `simp-declaration determinantZ2Charge_eq_negative_of_det_nonpos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L260 [soft] `skeletal-proof` in `theorem determinantZ2Charge_eq_negative_of_det_nonpos` — proof appears to close via minimal tactic one-liner
  - L288 [soft] `skeletal-proof` in `theorem determinant_sq_eq_one` — proof appears to close via minimal tactic one-liner
  - L301 [advisory] `local-hypothesis-injection` in `theorem determinant_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L304 [advisory] `local-hypothesis-injection` in `theorem determinant_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L320 [advisory] `local-hypothesis-injection` in `theorem determinant_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L342 [advisory] `local-hypothesis-injection` in `theorem determinant_eq_one_or_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L372 [soft] `skeletal-proof` in `theorem topologicalCharge_eq_one_of_det_eq_one` — proof appears to close via minimal tactic one-liner
  - L380 [soft] `skeletal-proof` in `theorem topologicalCharge_eq_neg_one_of_det_eq_neg_one` — proof appears to close via minimal tactic one-liner
  - L400 [soft] `simp-law-injection` in `simp-declaration determinantZ2Charge_eq_positive_of_det_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L402 [soft] `skeletal-proof` in `theorem determinantZ2Charge_eq_positive_of_det_pos` — proof appears to close via minimal tactic one-liner
  - L408 [soft] `simp-law-injection` in `simp-declaration determinantZ2Charge_eq_negative_of_det_nonpos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L410 [soft] `skeletal-proof` in `theorem determinantZ2Charge_eq_negative_of_det_nonpos` — proof appears to close via minimal tactic one-liner
  - L450 [soft] `law-field-locker` in `structure-field ChiralOrientationCalibration.positive_preserves` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L455 [soft] `law-field-locker` in `structure-field ChiralOrientationCalibration.negative_reverses` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L511 [soft] `law-field-locker` in `structure-field ChiralDeterminantChargeBridge.chi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L530 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L545 [advisory] `local-hypothesis-injection` in `theorem grading_det_eq_one_or_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L551 [advisory] `local-hypothesis-injection` in `theorem grading_det_eq_one_or_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L588 [soft] `law-field-locker` in `structure-field ChiralTopologicalChargeBridge.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L592 [soft] `law-field-locker` in `structure-field ChiralTopologicalChargeBridge.J_chi_compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L595 [soft] `law-field-locker` in `structure-field ChiralTopologicalChargeBridge.charge_detects_chiral_orientation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

