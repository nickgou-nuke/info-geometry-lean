# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:00.947016+00:00`
Root: `lean/InfoGeometry/Canonical/DiscreteModularSpectrum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **6**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DiscreteModularSpectrum.lean` | `advisory` | 20 | 0 | 6 | 8 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/DiscreteModularSpectrum.lean`
- module: `InfoGeometry.Canonical.DiscreteModularSpectrum`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field TypeIIIScaleGroup.add_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field TypeIIIScaleGroup.neg_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field DiscreteTypeIIILambdaScale.hq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [advisory] `existential-packaging` in `def spectrum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L85 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L87 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L98 [soft] `law-field-locker` in `structure-field ModularMellinLattice.K0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field ModularMellinLattice.commutes_with_drazin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L121 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L123 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L148 [soft] `skeletal-proof` in `theorem modularTransportGenerator_commutes_drazin` — proof appears to close via minimal tactic one-liner
  - L211 [advisory] `existential-packaging` in `def IsMellinBandlimited` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

