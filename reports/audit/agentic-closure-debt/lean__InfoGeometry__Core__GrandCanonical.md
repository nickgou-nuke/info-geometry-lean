# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:24.193971+00:00`
Root: `lean/InfoGeometry/Core/GrandCanonical.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **0**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/GrandCanonical.lean` | `advisory` | 7 | 0 | 0 | 7 | 7 |

## Findings by file

### `lean/InfoGeometry/Core/GrandCanonical.lean`
- module: `InfoGeometry.Core.GrandCanonical`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [advisory] `existential-packaging` in `abbrev GrandCanonicalTwoParam` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L67 [advisory] `existential-packaging` in `lemma gc_spinodal_iff_variance_eq_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L119 [advisory] `existential-packaging` in `lemma gc2_potential_deriv_mu_eq_beta_meanNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L178 [advisory] `existential-packaging` in `lemma gc2_muResponse_eq_beta_meanNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L185 [advisory] `existential-packaging` in `lemma gc2_responseMatrix_symmetric` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L192 [advisory] `existential-packaging` in `lemma gc2_responseMatrix_positiveSemidefinite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

