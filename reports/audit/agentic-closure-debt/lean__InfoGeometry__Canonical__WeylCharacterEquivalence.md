# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:11.193644+00:00`
Root: `lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **44**
- Hard: **0**
- Soft: **37**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean` | `advisory` | 81 | 0 | 37 | 7 | 44 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean`
- module: `InfoGeometry.Canonical.WeylCharacterEquivalence`
- status: `advisory`
- debt_score: `81`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `law-field-locker` in `structure-field ThermalRepresentation.thermalElement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field ThermalRepresentation.character` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field ThermalRepresentation.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field ThermalRepresentation.partitionFunction_eq_character` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field WeylRootSystem.positiveRootWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L73 [soft] `law-field-locker` in `structure-field PrimeRapidityEncoding.positiveRootToPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field PrimeRapidityEncoding.positiveRootToPrime_isPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field PrimeRapidityEncoding.primeRapidity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field PrimeRapidityEncoding.primeRapidity_eq_log` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field PrimeRapidityEncoding.rootWeight_eq_primeRapidity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field WeylDenominatorEulerProductBridge.denominator_eq_encoded_product` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L112 [soft] `law-field-locker` in `structure-field ParityTraceWitness.signature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field ParityTraceWitness.squareFree` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field ParityTraceWitness.squareFreeToWeyl` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field ParityTraceWitness.signature_eq_mobius` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L138 [soft] `law-field-locker` in `structure-field DeformedSouriauWeylCharacter.undeformed_eq_partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field DeformedSouriauWeylCharacter.deformation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field SouriauWeylPartitionPacket.deformed_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L179 [advisory] `bridge-shaped-declaration` in `theorem parity_trace_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L195 [soft] `law-field-locker` in `structure-field WeylDenominatorPrimeModePacket.product_eq_euler` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field SouriauThermalPrimeEvaluation.e_neg_alpha_eq_p_neg_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field InverseZetaWeylParitySupertrace.thermalEvaluationWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field InverseZetaWeylParitySupertrace.inverseZeta_eq_weylDenominator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field InverseZetaWeylParitySupertrace.weylDenominator_eq_paritySupertrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L245 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L264 [soft] `law-field-locker` in `structure-field BosonicZetaPartitionReciprocal.zeta_mul_bosonicPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L284 [soft] `law-field-locker` in `structure-field PrimeIndexedSouriauThermalEvaluation.thermalEvaluationRule` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field PrimeIndexedSouriauThermalEvaluation.inverseZeta_eq_primeIndexedWeylDenominator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field PrimeIndexedSouriauThermalEvaluation.inverseZeta_eq_paritySupertrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field PrimeIndexedSouriauThermalEvaluation.zeta_eq_reciprocalBosonicPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L332 [soft] `law-field-locker` in `structure-field CorrectedSouriauWeylSupertracePacket.p_neg_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [soft] `law-field-locker` in `structure-field CorrectedSouriauWeylSupertracePacket.parityTrace_is_denominator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field CorrectedSouriauWeylSupertracePacket.bosonTrace_separate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L337 [soft] `law-field-locker` in `structure-field CorrectedSouriauWeylSupertracePacket.fermionTrace_separate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [soft] `law-field-locker` in `structure-field SplitWeylParitySupertracePacket.inverseZeta_eq_paritySupertrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [soft] `law-field-locker` in `structure-field SplitWeylParitySupertracePacket.paritySupertrace_eq_parityTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L387 [soft] `law-field-locker` in `structure-field SplitCorrectedSouriauWeylSupertracePacket.p_neg_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L388 [soft] `law-field-locker` in `structure-field SplitCorrectedSouriauWeylSupertracePacket.parityTrace_is_denominator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L393 [soft] `law-field-locker` in `structure-field SplitCorrectedSouriauWeylSupertracePacket.inverseZeta_eq_paritySupertrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

