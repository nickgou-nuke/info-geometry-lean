# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:50.929609+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralDiracHomologyBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **14**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralDiracHomologyBridge.lean` | `advisory` | 40 | 0 | 14 | 12 | 26 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralDiracHomologyBridge.lean`
- module: `InfoGeometry.Canonical.ChiralDiracHomologyBridge`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field ChiralComplexSocket.dPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field ChiralComplexSocket.dMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field ChiralComplexSocket.dPlus_dMinus_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field ChiralComplexSocket.dMinus_dPlus_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [advisory] `existential-packaging` in `def plusBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L74 [advisory] `existential-packaging` in `def minusBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L122 [soft] `law-field-locker` in `structure-field ChiralHodgeDiracSocket.Dplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field ChiralHodgeDiracSocket.Dminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field ChiralHodgeDiracSocket.LapPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field ChiralHodgeDiracSocket.LapMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field ChiralHodgeDiracSocket.LapPlus_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `law-field-locker` in `structure-field ChiralHodgeDiracSocket.LapMinus_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L184 [soft] `law-field-locker` in `structure-field ChiralHodgeHomologyCalibration.Dplus_eq_dPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field ChiralHodgeHomologyCalibration.Dminus_eq_dMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field ChiralHodgeHomologyCalibration.plus_harmonic_represents_homology` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field ChiralHodgeHomologyCalibration.minus_harmonic_represents_homology` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L209 [advisory] `bridge-shaped-declaration` in `theorem plus_hodge_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L215 [advisory] `bridge-shaped-declaration` in `theorem minus_hodge_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L227 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L229 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L282 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L284 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

