# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:39.360247+00:00`
Root: `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean`
- module: `InfoGeometry.Canonical.AnomalyDilationBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L32 [soft] `skeletal-proof` in `theorem dilation_anomaly_jacobi_expansion` — proof appears to close via minimal tactic one-liner
  - L51 [soft] `skeletal-proof` in `theorem trace_dilation_eq_zero` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `local-hypothesis-injection` in `theorem normal_phase_of_trace_anomaly_in_finite_dim` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `local-hypothesis-injection` in `theorem normal_phase_of_trace_anomaly_in_finite_dim` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

