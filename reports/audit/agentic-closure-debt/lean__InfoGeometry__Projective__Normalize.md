# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.102649+00:00`
Root: `lean/InfoGeometry/Projective/Normalize.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Normalize.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Projective/Normalize.lean`
- module: `InfoGeometry.Projective.Normalize`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `existential-packaging` in `def normalizeOnProj` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L44 [soft] `simp-law-injection` in `simp-declaration normalizeOnProj_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration Z_normalizeOnProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration normalizeOnProj_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration Z_normalizeOnProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

