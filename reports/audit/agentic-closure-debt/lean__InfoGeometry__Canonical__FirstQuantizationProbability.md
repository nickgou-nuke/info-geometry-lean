# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:08.390434+00:00`
Root: `lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean`
- module: `InfoGeometry.Canonical.FirstQuantizationProbability`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L66 [soft] `simp-law-injection` in `simp-declaration classicalSurprisal_eq_relativeModularPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L159 [soft] `simp-law-injection` in `simp-declaration vacuumExpectation_eq_inner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [advisory] `existential-packaging` in `theorem vacuumExpectation_eq_inner` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L162 [soft] `skeletal-proof` in `theorem vacuumExpectation_eq_inner` — proof appears to close via minimal tactic one-liner
  - L172 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

