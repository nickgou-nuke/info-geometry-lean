# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:48.607039+00:00`
Root: `lean/InfoGeometry/Krein/Automorphisms.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Automorphisms.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Krein/Automorphisms.lean`
- module: `InfoGeometry.Krein.Automorphisms`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `simp-law-injection` in `simp-declaration conjugateCLM_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L27 [soft] `simp-law-injection` in `simp-declaration conjugateCLM_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L31 [soft] `simp-law-injection` in `simp-declaration conjugateCLM_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `simp-law-injection` in `simp-declaration conjugateCLM_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration conjugateCLM_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration conjugateCLM_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

