# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:30.343243+00:00`
Root: `lean/InfoGeometry/Application/BlackHoleEntropyReadout.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **17**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Application/BlackHoleEntropyReadout.lean` | `advisory` | 35 | 0 | 17 | 1 | 18 |

## Findings by file

### `lean/InfoGeometry/Application/BlackHoleEntropyReadout.lean`
- module: `InfoGeometry.Application.BlackHoleEntropyReadout`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `law-field-locker` in `structure-field BlackHoleEntropyReadout.splitChiralCompat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field BlackHoleEntropyReadout.thermoChiralCompat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field BlackHoleEntropyReadout.thermoNarainCompat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `simp-law-injection` in `simp-declaration entropyReadout_eq_supervolumeReadout` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `skeletal-proof` in `theorem entropyReadout_eq_supervolumeReadout` — proof appears to close via minimal tactic one-liner
  - L106 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_eq_negativeLogModularOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `skeletal-proof` in `theorem modularHamiltonian_eq_negativeLogModularOperator` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `simp-law-injection` in `simp-declaration negativeLogPotential_eq_narain` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [soft] `simp-law-injection` in `simp-declaration negativeLogPotential_eq_neg_log_narainSupervolumeReadout` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `skeletal-proof` in `theorem negativeLogPotential_eq_neg_log_narainSupervolumeReadout` — proof appears to close via minimal tactic one-liner
  - L124 [soft] `simp-law-injection` in `simp-declaration splitParity_eq_chiralParity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration splitParity_linearMap_eq_chiralParity_linearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L141 [soft] `simp-law-injection` in `simp-declaration thermo_modularHamiltonian_apply_eq_chiral` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L147 [soft] `simp-law-injection` in `simp-declaration thermo_supervolumeReadout_eq_narainSupervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L153 [soft] `simp-law-injection` in `simp-declaration entropyReadout_eq_narainSupervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L155 [soft] `skeletal-proof` in `theorem entropyReadout_eq_narainSupervolume` — proof appears to close via minimal tactic one-liner
  - L159 [soft] `simp-law-injection` in `simp-declaration negativeLogPotential_eq_neg_log_entropyReadout` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

