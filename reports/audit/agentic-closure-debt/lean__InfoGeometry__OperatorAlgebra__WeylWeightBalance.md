# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:26.769288+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/WeylWeightBalance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **16**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/WeylWeightBalance.lean` | `advisory` | 33 | 0 | 16 | 1 | 17 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/WeylWeightBalance.lean`
- module: `InfoGeometry.OperatorAlgebra.WeylWeightBalance`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `simp-law-injection` in `simp-declaration weight_m2` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `skeletal-proof` in `theorem weight_m2` — proof appears to close via minimal tactic one-liner
  - L53 [soft] `simp-law-injection` in `simp-declaration weight_m1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `skeletal-proof` in `theorem weight_m1` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `simp-law-injection` in `simp-declaration weight_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `skeletal-proof` in `theorem weight_zero` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `simp-law-injection` in `simp-declaration weight_p1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `theorem weight_p1` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration weight_p2` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `skeletal-proof` in `theorem weight_p2` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `skeletal-proof` in `theorem p2_m2_balanced` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem m2_p2_balanced` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem p1_m1_balanced` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `skeletal-proof` in `theorem m1_p1_balanced` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `theorem zero_zero_balanced` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `law-field-locker` in `structure-field WeylGradedCarrier.gradeOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

