# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:38.346701+00:00`
Root: `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **6**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean` | `advisory` | 17 | 0 | 6 | 5 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean`
- module: `InfoGeometry.Canonical.AlgebraicStateFunctionalBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [soft] `law-field-locker` in `structure-field PositiveNormalizedFunctional.probe` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field PositiveNormalizedFunctional.normalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `skeletal-proof` in `theorem ofNormalizedVectorState_probe_apply` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `law-field-locker` in `structure-field RepresentationFrame.coordinate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field StateRepresentationBridge.probe_eq_referenceExpectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L149 [soft] `skeletal-proof` in `theorem withFrame_probe_eq` — proof appears to close via minimal tactic one-liner

