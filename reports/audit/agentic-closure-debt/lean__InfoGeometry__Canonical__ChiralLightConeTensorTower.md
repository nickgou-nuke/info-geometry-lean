# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:52.201156+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralLightConeTensorTower.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralLightConeTensorTower.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralLightConeTensorTower.lean`
- module: `InfoGeometry.Canonical.ChiralLightConeTensorTower`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L87 [soft] `simp-law-injection` in `simp-declaration flip_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `simp-law-injection` in `simp-declaration toSymbol_flip_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `skeletal-proof` in `theorem toSymbol_flip_plus` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `simp-law-injection` in `simp-declaration toSymbol_flip_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `skeletal-proof` in `theorem toSymbol_flip_minus` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `simp-law-injection` in `simp-declaration CausalWord.toBoundary_of_lt` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L131 [soft] `skeletal-proof` in `theorem CausalWord.toBoundary_of_lt` — proof appears to close via minimal tactic one-liner
  - L135 [soft] `simp-law-injection` in `simp-declaration CausalWord.toChiralWord_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `skeletal-proof` in `theorem CausalWord.toChiralWord_apply` — proof appears to close via minimal tactic one-liner

