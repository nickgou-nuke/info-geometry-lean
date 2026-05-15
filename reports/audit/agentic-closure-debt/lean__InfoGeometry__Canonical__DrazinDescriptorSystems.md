# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:02.319614+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean`
- module: `InfoGeometry.Canonical.DrazinDescriptorSystems`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L72 [soft] `simp-law-injection` in `simp-declaration ambientGenerator_eq_coreGenerator_add_nilpotentGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `simp-law-injection` in `simp-declaration ambientFlow_eq_coreFlow_mul_nilpotentFlow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [soft] `simp-law-injection` in `simp-declaration ambientFlow_eq_nilpotentFlow_mul_coreFlow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

