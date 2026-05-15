# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:22.260997+00:00`
Root: `lean/InfoGeometry/Canonical/KKTGeneralizedMetricBridge.lean`
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
| `lean/InfoGeometry/Canonical/KKTGeneralizedMetricBridge.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/KKTGeneralizedMetricBridge.lean`
- module: `InfoGeometry.Canonical.KKTGeneralizedMetricBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [soft] `simp-law-injection` in `simp-declaration canonical_plusProjector_eq_generalizedMetric_plusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration canonical_minusProjector_eq_generalizedMetric_minusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

