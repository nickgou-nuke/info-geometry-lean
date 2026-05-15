# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.592897+00:00`
Root: `lean/InfoGeometry/Projective/Projective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Projective.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Projective/Projective.lean`
- module: `InfoGeometry.Projective.Projective`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `existential-packaging` in `def SameRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L60 [soft] `simp-law-injection` in `simp-declaration Z_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [advisory] `existential-packaging` in `lemma Z_scale` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L72 [soft] `simp-law-injection` in `simp-declaration normalize_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

