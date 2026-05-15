# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:21.335835+00:00`
Root: `lean/InfoGeometry/Canonical/JaynesRNModularBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **1**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/JaynesRNModularBridge.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/JaynesRNModularBridge.lean`
- module: `InfoGeometry.Canonical.JaynesRNModularBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L29 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L55 [advisory] `local-hypothesis-injection` in `theorem scalarModularPotential_exp_potential_div_partition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [advisory] `local-hypothesis-injection` in `theorem neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L103 [advisory] `local-hypothesis-injection` in `theorem potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

