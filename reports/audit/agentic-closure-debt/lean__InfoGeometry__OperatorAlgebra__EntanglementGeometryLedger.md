# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:13.402668+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/EntanglementGeometryLedger.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **16**
- Advisory: **19**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/EntanglementGeometryLedger.lean` | `advisory` | 51 | 0 | 16 | 19 | 35 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/EntanglementGeometryLedger.lean`
- module: `InfoGeometry.OperatorAlgebra.EntanglementGeometryLedger`
- status: `advisory`
- debt_score: `51`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `law-field-locker` in `structure-field MaxEntanglementRelation.Entangled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field MaxEntanglementRelation.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field MaxEntanglementRelation.monogamy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L124 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L162 [advisory] `existential-packaging` in `structure EntanglementConnectivityBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L175 [soft] `law-field-locker` in `structure-field EntanglementConnectivityBridge.ConnectedBy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field EntanglementConnectivityBridge.connected_of_entangled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field EntanglementConnectivityBridge.entangled_of_connected` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L195 [advisory] `bridge-shaped-declaration` in `theorem exists_bridge_of_entangled` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L195 [advisory] `existential-packaging` in `theorem exists_bridge_of_entangled` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L204 [advisory] `bridge-shaped-declaration` in `theorem no_bridge_of_not_entangled` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L204 [advisory] `existential-packaging` in `theorem no_bridge_of_not_entangled` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L218 [advisory] `existential-packaging` in `structure NonTraversableERRoute` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L233 [soft] `law-field-locker` in `structure-field NonTraversableERRoute.ExteriorSignal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field NonTraversableERRoute.InteriorMeeting` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field NonTraversableERRoute.no_exterior_signal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field NonTraversableERRoute.interior_meeting_possible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L259 [advisory] `existential-packaging` in `theorem exists_interior_meeting` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L297 [soft] `law-field-locker` in `structure-field TripartiteEntanglementPattern.tripartite_correlation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L337 [soft] `law-field-locker` in `structure-field ComplexityLedger.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [soft] `law-field-locker` in `structure-field ComplexityLedger.complexity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [soft] `law-field-locker` in `structure-field ComplexityLedger.thermalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L380 [advisory] `local-hypothesis-injection` in `theorem not_complexity_constant_on_thermal_window` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L398 [soft] `law-field-locker` in `structure-field ERBridgeGrowthComplexityCalibration.bridgeGrowthReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L401 [soft] `law-field-locker` in `structure-field ERBridgeGrowthComplexityCalibration.bridge_growth_eq_complexity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L411 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L412 [advisory] `bridge-shaped-declaration` in `theorem bridge_growth_changes_of_complexity_growth` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L412 [advisory] `placeholder-naming` in `theorem bridge_growth_changes_of_complexity_growth` — declaration name indicates temporary/external hypothesis surface
  - L424 [advisory] `bridge-shaped-declaration` in `theorem not_bridge_growth_constant_on_thermal_window` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

