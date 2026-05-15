# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:36.266017+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorJKOStep.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **34**
- Hard: **0**
- Soft: **24**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorJKOStep.lean` | `advisory` | 58 | 0 | 24 | 10 | 34 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorJKOStep.lean`
- module: `InfoGeometry.Canonical.OperatorJKOStep`
- status: `advisory`
- debt_score: `58`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field OperatorJKOPotential.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field OperatorJKOPotential.penalty` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field OperatorJKOPotential.penalty_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field OperatorJKOPotential.penalty_self_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L68 [soft] `simp-law-injection` in `simp-declaration objective_previous` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `skeletal-proof` in `theorem objective_previous` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `law-field-locker` in `structure-field OperatorJKOArgmin.stepSize_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field OperatorJKOArgmin.minimizing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L117 [soft] `skeletal-proof` in `theorem objective_le_previous_energy` — proof appears to close via minimal tactic one-liner
  - L127 [advisory] `local-hypothesis-injection` in `theorem energy_next_le_previous_energy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `theorem energy_next_le_previous_energy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [advisory] `local-hypothesis-injection` in `theorem penalty_le_energy_drop` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [soft] `law-field-locker` in `structure-field OperatorJKOArgminBackend.select` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field OperatorJKOArgminBackend.selected_previous` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field OperatorJKOArgminBackend.selected_stepSize` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field OperatorJKOPath.step` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L218 [soft] `law-field-locker` in `structure-field JKOBayesianCalibration.bayesUpdate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field JKOBayesianCalibration.stepSize` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field JKOBayesianCalibration.jkoStep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [soft] `law-field-locker` in `structure-field JKOBayesianCalibration.bayes_eq_jko_next` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [soft] `law-field-locker` in `structure-field JKOBayesianCalibration.jko_previous` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field JKOBayesianCalibration.jko_stepSize` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L249 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L302 [soft] `law-field-locker` in `structure-field NoisyJKOUpdate.correction_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L315 [soft] `section-law-variable` in `variable N` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L341 [soft] `law-field-locker` in `structure-field JKOModularFlowLimitCalibration.limit_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L354 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L354 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

