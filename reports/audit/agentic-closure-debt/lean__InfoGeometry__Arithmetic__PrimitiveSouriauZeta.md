# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:33.884955+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimitiveSouriauZeta.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **18**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimitiveSouriauZeta.lean` | `advisory` | 39 | 0 | 18 | 3 | 21 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimitiveSouriauZeta.lean`
- module: `InfoGeometry.Arithmetic.PrimitiveSouriauZeta`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `skeletal-proof` in `theorem primitiveFiniteZetaPartition_eq_sum` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `simp-law-injection` in `simp-declaration primitiveFiniteZetaPartition_empty` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration primitiveFiniteZetaPartition_singleton` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem primitiveFiniteZetaPartition_eq_arithmeticPartition_unit` — proof appears to close via minimal tactic one-liner
  - L89 [advisory] `local-hypothesis-injection` in `theorem primitiveFiniteZetaPartition_eq_exp_sum_of_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L91 [soft] `skeletal-proof` in `theorem primitiveWeightSum_eq_integral_finiteZetaPartition` — proof appears to close via minimal tactic one-liner
  - L137 [soft] `skeletal-proof` in `theorem objective_eq_integral_partition` — proof appears to close via minimal tactic one-liner
  - L144 [soft] `skeletal-proof` in `theorem objective_nonneg` — proof appears to close via minimal tactic one-liner
  - L163 [soft] `law-field-locker` in `structure-field FinitePrimitiveMaxEntWitness.maximizes_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `simp-law-injection` in `simp-declaration candidateAdmissible_objective` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L213 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.stateOfFinset` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L215 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.partitionReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.entropyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.objectiveReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.freeEnergyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.partition_eq_finiteZetaPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.objective_eq_primitiveWeightSum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.entropy_eq_objective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field PrimitiveSouriauZetaCalibration.freeEnergy_eq_objective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

