# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:27.018071+00:00`
Root: `lean/InfoGeometry/Optics/FiniteJonesBregman.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Optics/FiniteJonesBregman.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Optics/FiniteJonesBregman.lean`
- module: `InfoGeometry.Optics.FiniteJonesBregman`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L141 [soft] `skeletal-proof` in `theorem frobeniusBregmanRaw_eq_frobeniusBregman` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `simp-law-injection` in `simp-declaration frobeniusBregman_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L175 [soft] `skeletal-proof` in `theorem frobeniusBregman_self` — proof appears to close via minimal tactic one-liner
  - L194 [soft] `skeletal-proof` in `theorem frobeniusBregman_to_zero` — proof appears to close via minimal tactic one-liner

