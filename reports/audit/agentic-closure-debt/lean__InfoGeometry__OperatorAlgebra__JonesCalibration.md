# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:16.435514+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **22**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean` | `advisory` | 45 | 0 | 22 | 1 | 23 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean`
- module: `InfoGeometry.OperatorAlgebra.JonesCalibration`
- status: `advisory`
- debt_score: `45`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L152 [soft] `law-field-locker` in `structure-field JonesOpticalEvent.coherence_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `simp-law-injection` in `simp-declaration jones_apply_same_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `skeletal-proof` in `theorem jones_apply_same_zero` — proof appears to close via minimal tactic one-liner
  - L175 [soft] `simp-law-injection` in `simp-declaration jones_apply_same_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [soft] `skeletal-proof` in `theorem jones_apply_same_one` — proof appears to close via minimal tactic one-liner
  - L182 [soft] `simp-law-injection` in `simp-declaration jones_apply_offdiag_zero_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [soft] `skeletal-proof` in `theorem jones_apply_offdiag_zero_one` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `simp-law-injection` in `simp-declaration jones_apply_offdiag_one_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L192 [soft] `skeletal-proof` in `theorem jones_apply_offdiag_one_zero` — proof appears to close via minimal tactic one-liner
  - L298 [soft] `law-field-locker` in `structure-field V4OpticalCalibration.tag_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field V4OpticalCalibration.channel_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L326 [soft] `law-field-locker` in `structure-field TIRCalibration.tir_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L334 [soft] `law-field-locker` in `structure-field MetalMirrorCalibration.metal_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field MetalMirrorCalibration.diattenuation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field ChiralMediumCalibration.circular_basis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field ChiralMediumCalibration.chiral_transport_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [soft] `law-field-locker` in `structure-field JonesObstructionCalibration.eventOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L363 [soft] `law-field-locker` in `structure-field JonesObstructionCalibration.obstruction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field JonesObstructionCalibration.flat_obstruction_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [soft] `law-field-locker` in `structure-field SpectralDivisorCharge.multiplicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L407 [soft] `law-field-locker` in `structure-field SpectralDivisorCharge.chargeOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L410 [soft] `law-field-locker` in `structure-field SpectralDivisorCharge.divisor_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

