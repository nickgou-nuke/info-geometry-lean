# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:48.341804+00:00`
Root: `lean/InfoGeometry/Thermodynamics/SouriauModularS.lean`
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
| `lean/InfoGeometry/Thermodynamics/SouriauModularS.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Thermodynamics/SouriauModularS.lean`
- module: `InfoGeometry.Thermodynamics.SouriauModularS`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `simp-law-injection` in `simp-declaration modularSLiftInversion_element` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `skeletal-proof` in `theorem modularSLiftInversion_element` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `simp-law-injection` in `simp-declaration unitImaginary_re` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration unitImaginary_im` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `skeletal-proof` in `theorem unitImaginary_stationary_modularS` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `theorem modularS_closure_unitImaginary` — proof appears to close via minimal tactic one-liner

