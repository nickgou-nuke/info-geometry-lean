# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:47.102879+00:00`
Root: `lean/InfoGeometry/Canonical/RGFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **6**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RGFlow.lean` | `advisory` | 15 | 0 | 6 | 3 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/RGFlow.lean`
- module: `InfoGeometry.Canonical.RGFlow`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `simp-law-injection` in `simp-declaration constantFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration generatedDiscreteFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration generatedDiscreteFlow_succ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L204 [soft] `simp-law-injection` in `simp-declaration betaFunction_constantFlow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L210 [soft] `simp-law-injection` in `simp-declaration dualDeriv_constantFlow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L230 [advisory] `existential-packaging` in `theorem exists_isStationaryAtScale_constantFlow` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L242 [advisory] `existential-packaging` in `theorem existsUnique_fixedPoint_of_contracting` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L254 [soft] `skeletal-proof` in `theorem tendsto_generatedDiscreteFlow_fixedPoint_of_contracting` — proof appears to close via minimal tactic one-liner

