# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:44.628312+00:00`
Root: `lean/InfoGeometry/Information/Basic.lean`
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
| `lean/InfoGeometry/Information/Basic.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Information/Basic.lean`
- module: `InfoGeometry.Information.Basic`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `law-field-locker` in `structure-field StatisticalFamily.model` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field StatisticalFamily.dominated` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field StatisticalFamily.decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `skeletal-proof` in `lemma logLikelihood_eq_neg_logDensity` — proof appears to close via minimal tactic one-liner

