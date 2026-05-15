# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:34.807047+00:00`
Root: `lean/InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **13**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean` | `advisory` | 27 | 0 | 13 | 1 | 14 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean`
- module: `InfoGeometry.Arithmetic.ZetaTraceSpecialization`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L94 [soft] `simp-law-injection` in `simp-declaration finiteZetaTraceSupertrace_eq_supervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `theorem finiteZetaTraceSupertrace_eq_supervolume` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `simp-law-injection` in `simp-declaration finitePrimeGasPartition_eq_denominator_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `skeletal-proof` in `theorem finitePrimeGasPartition_eq_denominator_inv` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `theorem primeFockSupertrace_eq_finiteEulerDenominator` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `law-field-locker` in `structure-field FiniteZetaTraceReadout.supertrace_eq_denominator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field FiniteZetaTraceReadout.partition_eq_denominator_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `law-field-locker` in `structure-field FiniteZetaTraceReadout.supervolume_eq_denominator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `simp-law-injection` in `simp-declaration canonical_supertrace_eq_denominator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L180 [soft] `simp-law-injection` in `simp-declaration canonical_partition_eq_denominator_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L186 [soft] `simp-law-injection` in `simp-declaration canonical_supervolume_eq_denominator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L200 [soft] `simp-law-injection` in `simp-declaration finiteZetaTraceEffectiveAction_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `skeletal-proof` in `theorem finiteZetaTraceEffectiveAction_def` — proof appears to close via minimal tactic one-liner

