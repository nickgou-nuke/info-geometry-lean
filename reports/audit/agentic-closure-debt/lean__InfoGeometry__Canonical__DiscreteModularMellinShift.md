# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:00.822428+00:00`
Root: `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **13**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean` | `advisory` | 30 | 0 | 13 | 4 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean`
- module: `InfoGeometry.Canonical.DiscreteModularMellinShift`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [soft] `skeletal-proof` in `theorem doubledRealComplexScalar_zero_one_eq_clockAxis` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `skeletal-proof` in `theorem doubledRealComplexScalar_one_zero_eq_id` — proof appears to close via minimal tactic one-liner
  - L62 [soft] `skeletal-proof` in `theorem doubledRealPhaseOperator_zero` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `simp-law-injection` in `simp-declaration doubledRealMajoranaPacket_J_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `skeletal-proof` in `theorem doubledRealMajoranaPacket_J_eq_modular_j` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `simp-law-injection` in `simp-declaration doubledRealMajoranaPacket_eps_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `skeletal-proof` in `theorem doubledRealMajoranaPacket_eps_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `simp-law-injection` in `simp-declaration doubledRealMajoranaPacket_K_eq_clockAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `law-field-locker` in `structure-field DoubledRealMellinShiftOperator.weyl_covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [soft] `law-field-locker` in `structure-field DoubledRealSuperMellinAlgebra.superHamiltonian_split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field CliffordSuperMellinPacket.total_eq_blocks` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field CliffordSuperMellinPacket.shiftActsOnBosonicBlock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `law-field-locker` in `structure-field CliffordSuperMellinPacket.shiftActsOnFermionicBlock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

