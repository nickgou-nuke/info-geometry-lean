# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:15.246443+00:00`
Root: `lean/InfoGeometry/Cartan/Involution.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **2**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Cartan/Involution.lean` | `advisory` | 10 | 0 | 2 | 6 | 8 |

## Findings by file

### `lean/InfoGeometry/Cartan/Involution.lean`
- module: `InfoGeometry.Cartan.Involution`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L48 [advisory] `local-hypothesis-injection` in `lemma Pplus_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L66 [advisory] `local-hypothesis-injection` in `lemma Pminus_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `local-hypothesis-injection` in `lemma Pplus_add_Pminus_eq_id` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `lemma Pplus_comp_Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [soft] `skeletal-proof` in `lemma Pplus_apply` — proof appears to close via minimal tactic one-liner
  - L106 [soft] `skeletal-proof` in `lemma Pminus_apply` — proof appears to close via minimal tactic one-liner

