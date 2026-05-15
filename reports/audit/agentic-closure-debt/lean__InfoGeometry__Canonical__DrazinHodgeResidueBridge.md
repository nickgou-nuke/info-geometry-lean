# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.441448+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinHodgeResidueBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **4**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinHodgeResidueBridge.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinHodgeResidueBridge.lean`
- module: `InfoGeometry.Canonical.DrazinHodgeResidueBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `law-field-locker` in `structure-field DrazinHodgeResidueCalibration.HarmonicProjector_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field DrazinHodgeResidueCalibration.harmonic_eq_drazinComplement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field DrazinHodgeResidueCalibration.harmonic_fixed_iff_delta_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [soft] `section-law-variable` in `variable R` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

