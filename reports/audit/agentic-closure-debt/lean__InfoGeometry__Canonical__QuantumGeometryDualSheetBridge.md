# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:46.457286+00:00`
Root: `lean/InfoGeometry/Canonical/QuantumGeometryDualSheetBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/QuantumGeometryDualSheetBridge.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/QuantumGeometryDualSheetBridge.lean`
- module: `InfoGeometry.Canonical.QuantumGeometryDualSheetBridge`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [soft] `skeletal-proof` in `theorem cramerRaoMetricOp_eq_quantumGeometryOp` — proof appears to close via minimal tactic one-liner
  - L27 [soft] `skeletal-proof` in `theorem dualSheetMetricOp_eq_dualSheetLift_quantumGeometryOp` — proof appears to close via minimal tactic one-liner
  - L38 [soft] `skeletal-proof` in `theorem dualSheetMetricOp_eq_dualSheetLift_cramerRaoMetricOp` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_dualSheetLift_quantumGeometryOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_dualSheetLift_quantumGeometryOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_dualSheetLift_quantumGeometryOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_dualSheetLift_quantumGeometryOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_dualSheetLift_quantumGeometryOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_dualSheetLift_quantumGeometryOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

