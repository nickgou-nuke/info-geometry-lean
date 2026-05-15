# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.051395+00:00`
Root: `lean/InfoGeometry/Geometry/EntanglementGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **39**
- Hard: **0**
- Soft: **30**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/EntanglementGeometry.lean` | `advisory` | 69 | 0 | 30 | 9 | 39 |

## Findings by file

### `lean/InfoGeometry/Geometry/EntanglementGeometry.lean`
- module: `InfoGeometry.Geometry.EntanglementGeometry`
- status: `advisory`
- debt_score: `69`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field MonogamousPairing.partner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field MonogamousPairing.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field MonogamousPairing.no_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L127 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L201 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L262 [soft] `law-field-locker` in `structure-field AMPSReadout.interior_identification` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L293 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L294 [advisory] `bridge-shaped-declaration` in `theorem exterior_interior_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L368 [soft] `simp-law-injection` in `simp-declaration opposite_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L370 [soft] `skeletal-proof` in `theorem opposite_left` — proof appears to close via minimal tactic one-liner
  - L373 [soft] `simp-law-injection` in `simp-declaration opposite_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L375 [soft] `skeletal-proof` in `theorem opposite_right` — proof appears to close via minimal tactic one-liner
  - L378 [soft] `simp-law-injection` in `simp-declaration opposite_opposite` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L405 [soft] `skeletal-proof` in `theorem left_exterior_to_right_interior` — proof appears to close via minimal tactic one-liner
  - L414 [soft] `skeletal-proof` in `theorem right_exterior_to_left_interior` — proof appears to close via minimal tactic one-liner
  - L529 [soft] `skeletal-proof` in `theorem bell_alice_bob` — proof appears to close via minimal tactic one-liner
  - L536 [soft] `skeletal-proof` in `theorem bell_bob_alice` — proof appears to close via minimal tactic one-liner
  - L560 [soft] `skeletal-proof` in `theorem measurement_creates_global_knot` — proof appears to close via minimal tactic one-liner
  - L619 [soft] `skeletal-proof` in `theorem complexity_nil` — proof appears to close via minimal tactic one-liner
  - L626 [soft] `skeletal-proof` in `theorem complexity_append_gate` — proof appears to close via minimal tactic one-liner
  - L635 [soft] `skeletal-proof` in `theorem complexity_append` — proof appears to close via minimal tactic one-liner
  - L692 [soft] `skeletal-proof` in `theorem bridgeLength_grow` — proof appears to close via minimal tactic one-liner
  - L712 [soft] `skeletal-proof` in `theorem bridgeLength_growByCircuit` — proof appears to close via minimal tactic one-liner
  - L740 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L740 [soft] `section-law-variable` in `variable gates` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L741 [soft] `skeletal-proof` in `theorem zero` — proof appears to close via minimal tactic one-liner
  - L748 [soft] `skeletal-proof` in `theorem succ` — proof appears to close via minimal tactic one-liner
  - L757 [soft] `skeletal-proof` in `theorem complexity_eq_time` — proof appears to close via minimal tactic one-liner
  - L793 [soft] `law-field-locker` in `structure-field CanonicalGrowingCircuitTrajectory.stepGate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L799 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L824 [soft] `skeletal-proof` in `theorem circuitAt_succ` — proof appears to close via minimal tactic one-liner
  - L833 [soft] `skeletal-proof` in `theorem complexityAt_eq_time` — proof appears to close via minimal tactic one-liner
  - L845 [soft] `skeletal-proof` in `theorem bridgeLengthAt_eq_time` — proof appears to close via minimal tactic one-liner
  - L877 [soft] `skeletal-proof` in `theorem bridgeLengthAt_eq_initial_add_time` — proof appears to close via minimal tactic one-liner
  - L924 [soft] `skeletal-proof` in `theorem quantumRecurrenceScale_eq_two_pow_quantumMaxComplexityScale` — proof appears to close via minimal tactic one-liner
  - L934 [soft] `skeletal-proof` in `theorem quantumMaxComplexityScale_eq_two_pow` — proof appears to close via minimal tactic one-liner

