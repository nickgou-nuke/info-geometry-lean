# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:24.498539+00:00`
Root: `lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean`
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
| `lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean`
- module: `InfoGeometry.Canonical.KreinDiracPolarizationBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `simp-law-injection` in `simp-declaration transportEnd_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `skeletal-proof` in `theorem transportDirac_sq_eq_transportMetricOp` — proof appears to close via minimal tactic one-liner
  - L64 [advisory] `local-hypothesis-injection` in `theorem transportDirac_sq_eq_transportMetricOp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L66 [advisory] `local-hypothesis-injection` in `theorem transportDirac_sq_eq_transportMetricOp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

