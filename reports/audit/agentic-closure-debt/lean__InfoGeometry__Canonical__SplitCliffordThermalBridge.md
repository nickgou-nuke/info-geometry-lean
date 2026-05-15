# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:01.372593+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **4**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean`
- module: `InfoGeometry.Canonical.SplitCliffordThermalBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `simp-law-injection` in `simp-declaration transportedThermalGenerator_eq_transportDirac_of_zeroChemicalPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration transportedThermalFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `skeletal-proof` in `theorem transportedThermalFlow_add` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `theorem transportedThermalGenerator_eq_transportDirac_of_vacuumTransported` — proof appears to close via minimal tactic one-liner

