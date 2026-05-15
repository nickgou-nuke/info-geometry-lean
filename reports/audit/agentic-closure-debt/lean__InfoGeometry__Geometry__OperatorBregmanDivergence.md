# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:38.530840+00:00`
Root: `lean/InfoGeometry/Geometry/OperatorBregmanDivergence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **19**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/OperatorBregmanDivergence.lean` | `advisory` | 42 | 0 | 19 | 4 | 23 |

## Findings by file

### `lean/InfoGeometry/Geometry/OperatorBregmanDivergence.lean`
- module: `InfoGeometry.Geometry.OperatorBregmanDivergence`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `simp-law-injection` in `simp-declaration coe_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `skeletal-proof` in `theorem coe_mk` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `simp-law-injection` in `simp-declaration operatorBregmanDivergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `skeletal-proof` in `theorem operatorBregmanDivergence_self` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `simp-law-injection` in `simp-declaration operatorBregmanSym_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L144 [soft] `skeletal-proof` in `theorem operatorBregmanSym_self` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `law-field-locker` in `structure-field OperatorBregmanConvexityDatum.first_order_lower_bound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field OperatorBregmanConvexityDatum.eq_zero_iff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [soft] `law-field-locker` in `structure-field ModularRegularConeFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field ModularRegularConeFlow.preserves_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L237 [soft] `law-field-locker` in `structure-field ModularRegularConeFlow.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field ModularRegularConeFlow.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L258 [soft] `simp-law-injection` in `simp-declaration mapPoint_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L260 [soft] `skeletal-proof` in `theorem mapPoint_zero` — proof appears to close via minimal tactic one-liner
  - L283 [soft] `simp-law-injection` in `simp-declaration modularBregmanEnergy_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L286 [soft] `skeletal-proof` in `theorem modularBregmanEnergy_zero` — proof appears to close via minimal tactic one-liner
  - L321 [soft] `law-field-locker` in `structure-field SecondVariationAtZero.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [soft] `law-field-locker` in `structure-field BregmanRicciFluxBridge.conePointOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field BregmanRicciFluxBridge.flux_eq_bregman_secondVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L385 [advisory] `existential-packaging` in `def OperatorBregmanConvexityOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L394 [advisory] `existential-packaging` in `def BregmanRicciFluxBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

