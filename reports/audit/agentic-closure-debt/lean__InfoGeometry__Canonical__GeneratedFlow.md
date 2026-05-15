# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:10.181178+00:00`
Root: `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GeneratedFlow.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
- module: `InfoGeometry.Canonical.GeneratedFlow`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `simp-law-injection` in `simp-declaration along_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration along_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration fromLogGenerator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration fromLogGenerator_eq_along_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `simp-law-injection` in `simp-declaration generate_eq_along` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration generate_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration respond_eq_fromLogGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `skeletal-proof` in `theorem respond_apply` — proof appears to close via minimal tactic one-liner

