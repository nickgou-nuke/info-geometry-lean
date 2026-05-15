# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:49.621047+00:00`
Root: `lean/InfoGeometry/Topology/FractalCantorFockWitness.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **55**
- Hard: **0**
- Soft: **36**
- Advisory: **19**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Topology/FractalCantorFockWitness.lean` | `advisory` | 91 | 0 | 36 | 19 | 55 |

## Findings by file

### `lean/InfoGeometry/Topology/FractalCantorFockWitness.lean`
- module: `InfoGeometry.Topology.FractalCantorFockWitness`
- status: `advisory`
- debt_score: `91`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.T` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.S` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.T_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.S_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.T_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.S_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.T_S_comm_ne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field TiltSwitchSystem.T_S_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L118 [soft] `law-field-locker` in `structure-field RealDoubledCantorCliffordRepresentation.gamma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field RealDoubledCantorCliffordRepresentation.gamma_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field RealDoubledCantorCliffordRepresentation.gamma_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field RealDoubledCantorCliffordRepresentation.stringFormulaWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L171 [soft] `law-field-locker` in `structure-field CelikKocakInfiniteFockWitness.equivalentToFock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L196 [soft] `law-field-locker` in `structure-field FiniteCantorPauliWitness.psiGamma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field FiniteCantorPauliWitness.gamma_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field FiniteCantorPauliWitness.gamma_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field FiniteCantorPauliWitness.pauliTensorProductRealization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L245 [soft] `law-field-locker` in `structure-field RealCARPair.nilpotent_annihilation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L248 [soft] `law-field-locker` in `structure-field RealCARPair.nilpotent_creation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [soft] `law-field-locker` in `structure-field RealCARPair.car` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L287 [advisory] `existential-packaging` in `structure CliffordToCARWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L293 [soft] `law-field-locker` in `structure-field CliffordToCARWitness.gammaA_is_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L296 [soft] `law-field-locker` in `structure-field CliffordToCARWitness.gammaB_is_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field CliffordToCARWitness.realDoubledPhaseCalibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L310 [advisory] `existential-packaging` in `theorem gammaA_generator` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L316 [advisory] `existential-packaging` in `theorem gammaB_generator` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L336 [advisory] `existential-packaging` in `structure DrazinArrowTiltSwitchCalibration` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L343 [soft] `law-field-locker` in `structure-field DrazinArrowTiltSwitchCalibration.uPlus_realized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field DrazinArrowTiltSwitchCalibration.uMinus_realized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field DrazinArrowTiltSwitchCalibration.mirror_realized_by_switch` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L356 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L360 [advisory] `existential-packaging` in `theorem uPlus_calibrated` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L366 [advisory] `existential-packaging` in `theorem uMinus_calibrated` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L372 [advisory] `existential-packaging` in `theorem mirror_calibrated` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L391 [soft] `law-field-locker` in `structure-field FractalCantorFockWitness.fockSocketClosed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L397 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L401 [advisory] `bridge-shaped-declaration` in `theorem closes_fock_socket` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L426 [soft] `law-field-locker` in `structure-field DrazinHorizon.p_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L429 [soft] `law-field-locker` in `structure-field DrazinHorizon.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L432 [soft] `law-field-locker` in `structure-field DrazinHorizon.p_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L443 [soft] `law-field-locker` in `structure-field DrazinGreenHarmonic.H_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L446 [soft] `law-field-locker` in `structure-field DrazinGreenHarmonic.H_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L473 [soft] `law-field-locker` in `structure-field FierzReadout.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L500 [soft] `law-field-locker` in `structure-field FiniteEndpointMetricGraphCompression.embedding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L501 [soft] `law-field-locker` in `structure-field FiniteEndpointMetricGraphCompression.endpointAddress` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field FiniteEndpointMetricGraphCompression.optimalityOrCompressionWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L508 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L512 [advisory] `bridge-shaped-declaration` in `theorem compression_witness_holds` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

