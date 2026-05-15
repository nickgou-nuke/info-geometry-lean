# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:38.460906+00:00`
Root: `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **8**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean` | `advisory` | 23 | 0 | 8 | 7 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean`
- module: `InfoGeometry.Canonical.AlgebraicStationarity`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L90 [soft] `simp-law-injection` in `simp-declaration isStationaryAlong_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `simp-law-injection` in `simp-declaration isAlgebraicallyStationary_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `skeletal-proof` in `theorem isStateAlgebraicallyStationary_iff_generatorStationarity` — proof appears to close via minimal tactic one-liner
  - L174 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L176 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L177 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L178 [soft] `simp-law-injection` in `simp-declaration operatorInformationFirstVariation_neg_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [soft] `simp-law-injection` in `simp-declaration operatorInformationFirstVariation_neg_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L231 [soft] `simp-law-injection` in `simp-declaration phaseAxisResponse_eq_neg_KVariation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L234 [soft] `skeletal-proof` in `theorem phaseAxisResponse_eq_neg_KVariation` — proof appears to close via minimal tactic one-liner
  - L243 [soft] `simp-law-injection` in `simp-declaration KVariation_phaseAxisResponse_eq_neg_modularCurvature` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

