# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.988754+00:00`
Root: `lean/InfoGeometry/LLM/PinCPTBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/PinCPTBridge.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/LLM/PinCPTBridge.lean`
- module: `InfoGeometry.LLM.PinCPTBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [soft] `law-field-locker` in `structure-field PinAction.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `skeletal-proof` in `theorem odd_implies_even_square` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `theorem conjugate_odd_eq_neg` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `theorem conjugate_even_square_eq_self` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem conjugate_involutive` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `skeletal-proof` in `theorem odd_iff_anticommutator_zero` — proof appears to close via minimal tactic one-liner

