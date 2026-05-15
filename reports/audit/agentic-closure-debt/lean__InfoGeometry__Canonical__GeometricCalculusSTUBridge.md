# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:10.608753+00:00`
Root: `lean/InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean`
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
| `lean/InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean`
- module: `InfoGeometry.Canonical.GeometricCalculusSTUBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [soft] `simp-law-injection` in `simp-declaration stuFreudenthalChargeGeometry_I4` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `theorem stuFreudenthalChargeGeometry_I4` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `simp-law-injection` in `simp-declaration stuQubitChargeGeometry_I4` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `skeletal-proof` in `theorem stuQubitChargeGeometry_I4` — proof appears to close via minimal tactic one-liner
  - L173 [advisory] `existential-packaging` in `def STUQubitBoundaryFluxOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

