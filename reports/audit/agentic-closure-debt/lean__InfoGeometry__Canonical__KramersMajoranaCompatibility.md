# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:23.985201+00:00`
Root: `lean/InfoGeometry/Canonical/KramersMajoranaCompatibility.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **7**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KramersMajoranaCompatibility.lean` | `advisory` | 18 | 0 | 7 | 4 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/KramersMajoranaCompatibility.lean`
- module: `InfoGeometry.Canonical.KramersMajoranaCompatibility`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [soft] `law-field-locker` in `structure-field KramersMajoranaCompatible.S` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field KramersMajoranaCompatible.M` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L42 [soft] `section-law-variable` in `variable X` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L53 [soft] `skeletal-proof` in `theorem majorana_closed_theta` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem majorana_closed_phasePartner` — proof appears to close via minimal tactic one-liner
  - L99 [soft] `skeletal-proof` in `theorem theta_eq_phaseReductionFactor_comp_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L110 [soft] `skeletal-proof` in `theorem majorana_closed_phaseReductionFactor` — proof appears to close via minimal tactic one-liner

