# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:33.807044+00:00`
Root: `lean/InfoGeometry/Quantum/EntanglementMonogamy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **29**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/EntanglementMonogamy.lean` | `advisory` | 69 | 0 | 29 | 11 | 40 |

## Findings by file

### `lean/InfoGeometry/Quantum/EntanglementMonogamy.lean`
- module: `InfoGeometry.Quantum.EntanglementMonogamy`
- status: `advisory`
- debt_score: `69`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `law-field-locker` in `structure-field BipartiteReadout.outcomeL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field BipartiteReadout.outcomeR` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field BipartiteReadout.correlation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field EntanglementDatum.MaxEntangled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field EntanglementDatum.correlation_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L114 [soft] `law-field-locker` in `structure-field ObservableCorrelationWitness.outcomeL_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field ObservableCorrelationWitness.outcomeR_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field ObservableCorrelationWitness.correlation_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L162 [soft] `law-field-locker` in `structure-field ReadoutEntanglementDatum.MaxEntangled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L201 [soft] `law-field-locker` in `structure-field MonogamyBackend.MaxEntangled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field MonogamyBackend.Independent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field MonogamyBackend.monogamy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L254 [soft] `law-field-locker` in `structure-field ERBridgeDatum.entangled_pair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L255 [soft] `law-field-locker` in `structure-field ERBridgeDatum.bridge_exists` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L256 [soft] `law-field-locker` in `structure-field ERBridgeDatum.exterior_to_exterior_signal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L257 [soft] `law-field-locker` in `structure-field ERBridgeDatum.interior_meeting_possible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [soft] `law-field-locker` in `structure-field ERBridgeDatum.bridge_of_entanglement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L260 [soft] `law-field-locker` in `structure-field ERBridgeDatum.nontraversable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L266 [advisory] `bridge-shaped-declaration` in `theorem bridge_exists_of_entangled` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L266 [advisory] `placeholder-naming` in `theorem bridge_exists_of_entangled` — declaration name indicates temporary/external hypothesis surface
  - L272 [advisory] `bridge-shaped-declaration` in `theorem no_exterior_signal_of_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L300 [soft] `law-field-locker` in `structure-field EREPRIdentification.Bridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [soft] `law-field-locker` in `structure-field EREPRIdentification.EncodedTogether` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field EREPRIdentification.encoded_of_bridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [soft] `law-field-locker` in `structure-field EREPRIdentification.not_independent_of_encoded` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L363 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.complexity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L365 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.bridgeLength` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.evolve` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L368 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.bridgeLength_eq_complexity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L371 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.entropy_saturated_after_thermalization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field ComplexityBridgeBackend.complexity_grows_after_thermalization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L385 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

