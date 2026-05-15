# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:39.485046+00:00`
Root: `lean/InfoGeometry/Geometry/RealRotorCore.lean`
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
| `lean/InfoGeometry/Geometry/RealRotorCore.lean` | `advisory` | 27 | 0 | 13 | 1 | 14 |

## Findings by file

### `lean/InfoGeometry/Geometry/RealRotorCore.lean`
- module: `InfoGeometry.Geometry.RealRotorCore`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `law-field-locker` in `structure-field SL2RMatrix.det_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `simp-law-injection` in `simp-declaration one_scalar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [soft] `skeletal-proof` in `theorem one_scalar` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration one_bivector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `skeletal-proof` in `theorem one_bivector` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `simp-law-injection` in `simp-declaration mul_scalar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `skeletal-proof` in `theorem mul_scalar` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `simp-law-injection` in `simp-declaration mul_bivector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem mul_bivector` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `simp-law-injection` in `simp-declaration normSq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `skeletal-proof` in `theorem normSq_one` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `law-field-locker` in `structure-field NormalizedRotor.normSq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field Spin2.unit_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

