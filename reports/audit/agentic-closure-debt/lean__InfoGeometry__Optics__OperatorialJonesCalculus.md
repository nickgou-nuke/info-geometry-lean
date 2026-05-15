# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:28.083009+00:00`
Root: `lean/InfoGeometry/Optics/OperatorialJonesCalculus.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **23**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Optics/OperatorialJonesCalculus.lean` | `advisory` | 51 | 0 | 23 | 5 | 28 |

## Findings by file

### `lean/InfoGeometry/Optics/OperatorialJonesCalculus.lean`
- module: `InfoGeometry.Optics.OperatorialJonesCalculus`
- status: `advisory`
- debt_score: `51`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field PolarizationProjectorPair.P_s_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field PolarizationProjectorPair.P_p_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field PolarizationProjectorPair.s_p_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field PolarizationProjectorPair.p_s_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field PolarizationProjectorPair.sum_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L158 [soft] `skeletal-proof` in `theorem brewsterReflector_eq` — proof appears to close via minimal tactic one-liner
  - L266 [soft] `law-field-locker` in `structure-field DeterministicJonesDatum.adj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field DeterministicJonesDatum.action` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [soft] `law-field-locker` in `structure-field DeterministicJonesDatum.action_eq_jones` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field ProjectiveJonesDatum.projectivelyEquivalent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field ProjectiveJonesDatum.projective_refl` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L303 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L334 [soft] `law-field-locker` in `structure-field BrewsterRankCollapse.R_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [soft] `law-field-locker` in `structure-field PhaseRetarderBranch.R_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L365 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L389 [soft] `law-field-locker` in `structure-field DiattenuatorBranch.R_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L407 [soft] `law-field-locker` in `structure-field PureRetarderBranch.s_unit_modulus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L411 [soft] `law-field-locker` in `structure-field PureRetarderBranch.p_unit_modulus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [soft] `law-field-locker` in `structure-field LossyMetalMirrorBranch.R_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L438 [soft] `law-field-locker` in `structure-field LossyMetalMirrorBranch.lossy_metal_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field PolarizationChannel.branchOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L457 [soft] `law-field-locker` in `structure-field PolarizationChannel.adj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L460 [soft] `law-field-locker` in `structure-field PolarizationChannel.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L463 [soft] `law-field-locker` in `structure-field PolarizationChannel.channel_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L474 [soft] `law-field-locker` in `structure-field RoughReflectionChannel.depolarizing_or_direction_mixing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L476 [advisory] `existential-packaging` in `def OperatorialJonesOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

