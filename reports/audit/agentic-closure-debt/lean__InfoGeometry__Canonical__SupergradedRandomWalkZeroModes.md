# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:04.756252+00:00`
Root: `lean/InfoGeometry/Canonical/SupergradedRandomWalkZeroModes.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **16**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SupergradedRandomWalkZeroModes.lean` | `advisory` | 34 | 0 | 16 | 2 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/SupergradedRandomWalkZeroModes.lean`
- module: `InfoGeometry.Canonical.SupergradedRandomWalkZeroModes`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [soft] `law-field-locker` in `structure-field SuperLattice.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field MarkovKernel.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field MarkovKernel.row_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field DrazinHodgeProjector.H_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field DrazinHodgeProjector.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `law-field-locker` in `structure-field DrazinHodgeProjector.H_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [soft] `law-field-locker` in `structure-field MonteCarloZeroModeEstimator.estimator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field SuperGaugeAction.parity_preserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field ZeroModeVolumeCalibration.volume_eq_zeroModeOrbits` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L253 [soft] `law-field-locker` in `structure-field SignalDrazinHorizon.p_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L256 [soft] `law-field-locker` in `structure-field SignalDrazinHorizon.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [soft] `law-field-locker` in `structure-field SignalDrazinHorizon.p_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `skeletal-proof` in `theorem matterEnvelope_eq` — proof appears to close via minimal tactic one-liner
  - L321 [soft] `law-field-locker` in `structure-field FierzReadout.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [soft] `law-field-locker` in `structure-field FierzKleinResidual.residual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L354 [soft] `law-field-locker` in `structure-field MatterEnvelopeFierzKleinAdmissible.residual_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L402 [advisory] `existential-packaging` in `def HodgeDrazinMonteCarloSocketTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

