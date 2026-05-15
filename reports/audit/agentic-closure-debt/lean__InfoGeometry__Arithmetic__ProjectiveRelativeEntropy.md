# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:34.277357+00:00`
Root: `lean/InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **17**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean` | `advisory` | 38 | 0 | 17 | 4 | 21 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean`
- module: `InfoGeometry.Arithmetic.ProjectiveRelativeEntropy`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `skeletal-proof` in `theorem primitiveToPrimeProjectiveKL_eq` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem primeToPrimitiveProjectiveKL_eq` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `law-field-locker` in `structure-field ProjectiveKLWitness.klReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field ProjectiveKLWitness.kl_eq_primitiveToPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field ProjectiveKLWitness.kl_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field ProjectiveKLWitness.candidate_ne_reference` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field ProjectiveKLWitness.kl_pos_of_ne_reference` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [soft] `law-field-locker` in `structure-field ProjectiveKLWitness.kl_zero_of_reference` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L167 [soft] `law-field-locker` in `structure-field IntegratedProjectiveKLWitness.integrated_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field IntegratedProjectiveKLWitness.integrated_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field IntegratedProjectiveKLWitness.integrated_pos_of_ne_reference` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L215 [soft] `law-field-locker` in `structure-field ProjectiveKLCalibration.stateOfPair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [soft] `law-field-locker` in `structure-field ProjectiveKLCalibration.klReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field ProjectiveKLCalibration.integratedKLReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field ProjectiveKLCalibration.witnessOfPair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field ProjectiveKLCalibration.pointwise_eq_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field ProjectiveKLCalibration.integrated_eq_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L245 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

