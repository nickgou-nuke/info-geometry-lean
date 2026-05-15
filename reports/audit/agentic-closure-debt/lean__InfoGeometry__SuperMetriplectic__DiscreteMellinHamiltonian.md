# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:42.483325+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/DiscreteMellinHamiltonian.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **16**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/DiscreteMellinHamiltonian.lean` | `advisory` | 36 | 0 | 16 | 4 | 20 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/DiscreteMellinHamiltonian.lean`
- module: `InfoGeometry.SuperMetriplectic.DiscreteMellinHamiltonian`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.linearSample` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.logarithmicSample` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.logCoordinate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.dftSpectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.dmtSpectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.log_sample_eq_coordinate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field LogSampledDFTMellinPacket.dmt_eq_dft_on_logSamples` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field DiscreteMellinModularHamiltonianPacket.context` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field DiscreteMellinModularHamiltonianPacket.mellinWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field DiscreteMellinModularHamiltonianPacket.mellinWeight_eq_discreteRapidity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field DiscreteMellinModularHamiltonianPacket.hamiltonianReadout_eq_context` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field DiscreteLorentzMellinQuantizationPacket.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field DiscreteLorentzMellinQuantizationPacket.samples_match_owner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field DiscreteLorentzMellinQuantizationPacket.logCoordinates_match_rapidity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field DiscreteMellinCasimirQuantizationPacket.zetaCasimirResidual_eq_mode_logGap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [advisory] `existential-packaging` in `theorem zetaCasimirResidual_quantized` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L207 [soft] `skeletal-proof` in `theorem thermal_gap_eq_log_q` — proof appears to close via minimal tactic one-liner

