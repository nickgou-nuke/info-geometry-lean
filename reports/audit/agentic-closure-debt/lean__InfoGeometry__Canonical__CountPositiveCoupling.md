# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:57.554054+00:00`
Root: `lean/InfoGeometry/Canonical/CountPositiveCoupling.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **0**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CountPositiveCoupling.lean` | `advisory` | 7 | 0 | 0 | 7 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/CountPositiveCoupling.lean`
- module: `InfoGeometry.Canonical.CountPositiveCoupling`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L9 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L11 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L44 [advisory] `local-hypothesis-injection` in `lemma entrywisePositive_hasPositiveRowSums` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L45 [advisory] `local-hypothesis-injection` in `lemma entrywisePositive_hasPositiveRowSums` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [advisory] `local-hypothesis-injection` in `lemma entrywisePositive_hasPositiveColSums` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L57 [advisory] `local-hypothesis-injection` in `lemma entrywisePositive_hasPositiveColSums` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

