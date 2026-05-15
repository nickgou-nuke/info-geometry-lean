# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:49.340458+00:00`
Root: `lean/InfoGeometry/Krein/BoundedKMSHestenesVacuumBridge.lean`
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
| `lean/InfoGeometry/Krein/BoundedKMSHestenesVacuumBridge.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Krein/BoundedKMSHestenesVacuumBridge.lean`
- module: `InfoGeometry.Krein.BoundedKMSHestenesVacuumBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesVacuumBridge.boundedHestenes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesVacuumBridge.realState_eq_vacuumRealState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L68 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

