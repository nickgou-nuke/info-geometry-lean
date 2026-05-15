# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.585023+00:00`
Root: `lean/InfoGeometry/KK/RealSplitKreinResolvent.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/RealSplitKreinResolvent.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/KK/RealSplitKreinResolvent.lean`
- module: `InfoGeometry.KK.RealSplitKreinResolvent`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field RealSplitKreinResolventData.resolvent_preserves_domain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field RealSplitKreinResolventData.left_resolvent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `simp-law-injection` in `simp-declaration resolvent_mem_domain` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration shiftedApply_resolvent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `skeletal-proof` in `lemma isCompactOperator` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `lemma comp_left_isCompactEnd` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `skeletal-proof` in `lemma comp_right_isCompactEnd` — proof appears to close via minimal tactic one-liner

