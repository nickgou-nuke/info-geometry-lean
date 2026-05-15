# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:51.060139+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralDiracHomologyCalibration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **9**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralDiracHomologyCalibration.lean` | `advisory` | 24 | 0 | 9 | 6 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralDiracHomologyCalibration.lean`
- module: `InfoGeometry.Canonical.ChiralDiracHomologyCalibration`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field ChiralDifferentialCalibration.dPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field ChiralDifferentialCalibration.dMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field ChiralDifferentialCalibration.dMinus_comp_dPlus_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field ChiralDifferentialCalibration.dPlus_comp_dMinus_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L52 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L67 [advisory] `existential-packaging` in `def IsPlusBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L72 [advisory] `existential-packaging` in `def IsMinusBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L116 [soft] `skeletal-proof` in `theorem plusHomologyEquivalent_symm` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `theorem plusHomologyEquivalent_trans` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `skeletal-proof` in `theorem minusHomologyEquivalent_symm` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `skeletal-proof` in `theorem minusHomologyEquivalent_trans` — proof appears to close via minimal tactic one-liner
  - L217 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L219 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

