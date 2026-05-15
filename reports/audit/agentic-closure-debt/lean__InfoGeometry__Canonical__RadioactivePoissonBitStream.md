# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:47.382167+00:00`
Root: `lean/InfoGeometry/Canonical/RadioactivePoissonBitStream.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **9**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RadioactivePoissonBitStream.lean` | `advisory` | 21 | 0 | 9 | 3 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/RadioactivePoissonBitStream.lean`
- module: `InfoGeometry.Canonical.RadioactivePoissonBitStream`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L114 [soft] `law-field-locker` in `structure-field RadioactiveDecayChannel.rate_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field RadioactiveDecayChannel.window_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L148 [soft] `law-field-locker` in `structure-field ParityPoissonCalibrationAssumption.oddProbability_eq_poisson` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field SpinorSocket.streams` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field RadioactiveSpinorSocket.channels` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field IndependentCenteredSpinorCalibration.centered` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field IndependentCenteredSpinorCalibration.covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field IndependentCenteredSpinorCalibration.centered_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [soft] `law-field-locker` in `structure-field IndependentCenteredSpinorCalibration.covariance_eq_delta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [advisory] `existential-packaging` in `def RadioactiveSpinorSocketTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

