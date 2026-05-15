# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:40.655412+00:00`
Root: `lean/InfoGeometry/Canonical/AssociativeSuperBracket.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **2**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AssociativeSuperBracket.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/AssociativeSuperBracket.lean`
- module: `InfoGeometry.Canonical.AssociativeSuperBracket`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `simp-law-injection` in `simp-declaration superBracket_even_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration superBracket_odd_odd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

