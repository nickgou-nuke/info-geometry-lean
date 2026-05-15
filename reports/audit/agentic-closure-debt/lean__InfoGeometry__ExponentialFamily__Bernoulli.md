# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:29.227636+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/Bernoulli.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **2**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ExponentialFamily/Bernoulli.lean` | `advisory` | 9 | 0 | 2 | 5 | 7 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/Bernoulli.lean`
- module: `InfoGeometry.ExponentialFamily.Bernoulli`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [soft] `skeletal-proof` in `lemma deriv_logPartition` — proof appears to close via minimal tactic one-liner
  - L19 [advisory] `local-hypothesis-injection` in `lemma deriv_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L33 [soft] `skeletal-proof` in `lemma bernoulli_metric` — proof appears to close via minimal tactic one-liner
  - L36 [advisory] `local-hypothesis-injection` in `lemma bernoulli_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L41 [advisory] `local-hypothesis-injection` in `lemma bernoulli_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L42 [advisory] `local-hypothesis-injection` in `lemma bernoulli_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

