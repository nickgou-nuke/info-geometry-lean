# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:53.343212+00:00`
Root: `lean/SelfReference/RobustThermodynamicRegression.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **1**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/SelfReference/RobustThermodynamicRegression.lean` | `advisory` | 6 | 0 | 1 | 4 | 5 |

## Findings by file

### `lean/SelfReference/RobustThermodynamicRegression.lean`
- module: `SelfReference.RobustThermodynamicRegression`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L57 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L95 [advisory] `existential-packaging` in `theorem phase_transition_catastrophe` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [soft] `skeletal-proof` in `theorem phase_transition_catastrophe` — proof appears to close via minimal tactic one-liner
  - L111 [advisory] `local-hypothesis-injection` in `theorem phase_transition_catastrophe` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

