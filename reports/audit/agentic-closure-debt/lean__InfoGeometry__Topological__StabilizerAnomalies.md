# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:49.229432+00:00`
Root: `lean/InfoGeometry/Topological/StabilizerAnomalies.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Topological/StabilizerAnomalies.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Topological/StabilizerAnomalies.lean`
- module: `InfoGeometry.Topological.StabilizerAnomalies`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `law-field-locker` in `structure-field StabilizerAnomalyData.stabilizes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field StabilizerAnomalyData.anomalyHom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `simp-law-injection` in `simp-declaration mapTarget_anomalyHom` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `skeletal-proof` in `theorem mapTarget_anomalyHom` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem stabilizerAnomalyAtI_hom` — proof appears to close via minimal tactic one-liner
  - L177 [soft] `skeletal-proof` in `theorem exactPhaseStabilizerAnomalyAtI_hom` — proof appears to close via minimal tactic one-liner

