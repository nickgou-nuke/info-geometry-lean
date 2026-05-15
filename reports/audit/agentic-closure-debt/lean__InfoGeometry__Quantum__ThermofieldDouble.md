# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:37.246488+00:00`
Root: `lean/InfoGeometry/Quantum/ThermofieldDouble.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **32**
- Hard: **0**
- Soft: **23**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/ThermofieldDouble.lean` | `advisory` | 55 | 0 | 23 | 9 | 32 |

## Findings by file

### `lean/InfoGeometry/Quantum/ThermofieldDouble.lean`
- module: `InfoGeometry.Quantum.ThermofieldDouble`
- status: `advisory`
- debt_score: `55`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [soft] `law-field-locker` in `structure-field FiniteQuantumSpectrum.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [advisory] `existential-packaging` in `theorem partition_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L36 [advisory] `existential-packaging` in `theorem partition_pos_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L41 [advisory] `existential-packaging` in `theorem sqrt_partition_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L60 [soft] `skeletal-proof` in `theorem tfdCoeff_zero_time` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem tfdCoeffSupported_eq_zero_of_not_mem` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `theorem tfdCoeffOnSupport_eq_supported` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `law-field-locker` in `structure-field BulkGeometry.isConnected` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field BulkGeometry.interiorVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field EREPRCalibration.isEPR` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [soft] `law-field-locker` in `structure-field EREPRCalibration.hasERBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field EREPRCalibration.realizes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field EREPRCalibration.er_of_epr` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field EREPRCalibration.epr_of_er` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L151 [soft] `law-field-locker` in `structure-field RyuTakayanagiCalibration.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field RyuTakayanagiCalibration.area` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [soft] `law-field-locker` in `structure-field RyuTakayanagiCalibration.extremalSurfaceOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field RyuTakayanagiCalibration.NewtonConstant_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `law-field-locker` in `structure-field RyuTakayanagiCalibration.entropy_eq_area_div` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L180 [soft] `law-field-locker` in `structure-field ExactERBridgeGrowth.linearGrowth` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `law-field-locker` in `structure-field PrimeBitSpectrum.prime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field PrimeBitSpectrum.isPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [advisory] `local-hypothesis-injection` in `theorem bitEnergy_eq_log_bitInteger` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L289 [soft] `law-field-locker` in `structure-field PrimitiveAntichainCalibration.primitive_iff_antichain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L296 [soft] `law-field-locker` in `structure-field ArithmeticModularCalibration.modular_hamiltonian_val` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field ArithmeticModularCalibration.profileOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `law-field-locker` in `structure-field ArithmeticModularCalibration.modular_eq_arithmetic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

