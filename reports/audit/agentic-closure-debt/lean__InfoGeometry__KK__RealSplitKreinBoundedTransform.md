# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.193784+00:00`
Root: `lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean`
- module: `InfoGeometry.KK.RealSplitKreinBoundedTransform`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `skeletal-proof` in `lemma isCompactEnd_neg` — proof appears to close via minimal tactic one-liner
  - L41 [soft] `skeletal-proof` in `lemma isCompactEnd_sub` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `lemma isCompactEnd_comp_right` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `skeletal-proof` in `lemma isCompactEnd_comp_left` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `law-field-locker` in `structure-field RealSplitKreinBoundedTransform.phase_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field RealSplitKreinBoundedTransform.phase_krein_skewAdj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L151 [soft] `simp-law-injection` in `simp-declaration phase_eq_resolvent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `simp-law-injection` in `simp-declaration toRealSplitKreinKasparovCycle_F` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [soft] `simp-law-injection` in `simp-declaration toKasparovCycle_F` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

