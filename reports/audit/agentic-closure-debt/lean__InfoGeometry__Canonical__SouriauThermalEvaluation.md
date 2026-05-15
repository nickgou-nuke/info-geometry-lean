# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:58.745774+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauThermalEvaluation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauThermalEvaluation.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauThermalEvaluation.lean`
- module: `InfoGeometry.Canonical.SouriauThermalEvaluation`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [soft] `law-field-locker` in `structure-field SouriauThermalEvaluation.p_neg_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field SouriauThermalEvaluation.e_neg_alpha` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field SouriauThermalEvaluation.e_neg_alpha_eq_p_neg_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field SouriauThermalEvaluation.pairing_eq_beta_log` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

