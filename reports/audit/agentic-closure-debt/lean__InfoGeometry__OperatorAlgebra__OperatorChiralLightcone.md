# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:19.612110+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/OperatorChiralLightcone.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **12**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/OperatorChiralLightcone.lean` | `advisory` | 30 | 0 | 12 | 6 | 18 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/OperatorChiralLightcone.lean`
- module: `InfoGeometry.OperatorAlgebra.OperatorChiralLightcone`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `simp-law-injection` in `simp-declaration opposite_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `skeletal-proof` in `theorem opposite_left` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `simp-law-injection` in `simp-declaration opposite_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `skeletal-proof` in `theorem opposite_right` — proof appears to close via minimal tactic one-liner
  - L170 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L291 [soft] `law-field-locker` in `structure-field ChiralLightconeMirror.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field ChiralLightconeMirror.q_preserving` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field ChiralLightconeMirror.maps_left_to_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [soft] `law-field-locker` in `structure-field ChiralLightconeMirror.maps_right_to_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L344 [advisory] `existential-packaging` in `structure OperatorDefectChiralLightconeBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L359 [soft] `law-field-locker` in `structure-field OperatorDefectChiralLightconeBridge.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [soft] `law-field-locker` in `structure-field OperatorDefectChiralLightconeBridge.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [soft] `law-field-locker` in `structure-field OperatorDefectChiralLightconeBridge.defect_maps_to_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L373 [soft] `law-field-locker` in `structure-field OperatorDefectChiralLightconeBridge.defect_hits_chiral_lightcone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L396 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L407 [advisory] `existential-packaging` in `theorem defect_has_chiral_lightlike_image` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

