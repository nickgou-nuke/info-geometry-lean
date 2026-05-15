# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:02.599584+00:00`
Root: `lean/InfoGeometry/Canonical/SuperAnomaly.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperAnomaly.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperAnomaly.lean`
- module: `InfoGeometry.Canonical.SuperAnomaly`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `simp-law-injection` in `simp-declaration superComm_even_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `simp-law-injection` in `simp-declaration superComm_odd_odd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `law-field-locker` in `structure-field SuperWeightLike.graded_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L78 [soft] `skeletal-proof` in `lemma graded_weight_anticommutator` — proof appears to close via minimal tactic one-liner

