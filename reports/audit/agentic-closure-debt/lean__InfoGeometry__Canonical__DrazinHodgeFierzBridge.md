# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.322338+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinHodgeFierzBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinHodgeFierzBridge.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinHodgeFierzBridge.lean`
- module: `InfoGeometry.Canonical.DrazinHodgeFierzBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [soft] `law-field-locker` in `structure-field DrazinHodgeFierzBridge.residue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field DrazinHodgeFierzBridge.toFierzState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field DrazinHodgeFierzBridge.geometricPredicate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field DrazinHodgeFierzBridge.geometricPredicate_on_envelope` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L77 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L247 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

