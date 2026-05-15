# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:57.676956+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **73**
- Hard: **0**
- Soft: **71**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean` | `advisory` | 144 | 0 | 71 | 2 | 73 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean`
- module: `InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport`
- status: `advisory`
- debt_score: `144`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field SouriauLieThermoData.momentMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field SouriauLieThermoData.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `skeletal-proof` in `theorem K_beta_eq_pairing` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem gibbsWeight_eq_exp_neg_K_beta` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `law-field-locker` in `structure-field SouriauTransportFlow.hamiltonianVectorField` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field SouriauTransportFlow.reversibleDensityTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field SouriauTransportFlow.reversibleTransport_eq_hamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field SouriauTransportFlow.preservesLiouvilleMeasure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field SouriauTransportFlow.preservesGibbsWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field SouriauTransportFlow.preservesEntropyFunctional` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field MetriplecticData.poissonBracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field MetriplecticData.metricBracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field MetriplecticData.poisson_skew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field MetriplecticData.poisson_jacobi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field MetriplecticData.metric_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field MetriplecticData.metric_positive_semidefinite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field MetriplecticData.entropy_is_poisson_casimir` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field MetriplecticData.energy_is_metric_casimir` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field MetriplecticData.entropyProductionNonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field MetriplecticConsistencyWitness.reversiblePreservesEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field MetriplecticConsistencyWitness.dissipativeProducesEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field MetriplecticConsistencyWitness.entropyProduction_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field OptimalTransportMetricWitness.cost` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [soft] `law-field-locker` in `structure-field OptimalTransportMetricWitness.mobilityOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `law-field-locker` in `structure-field OptimalTransportMetricWitness.wassersteinMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `law-field-locker` in `structure-field OptimalTransportMetricWitness.continuityEquation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `law-field-locker` in `structure-field OptimalTransportMetricWitness.transportRegularity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field OptimalTransportMetricWitness.metricPositiveSemidefinite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.entropyTerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.expectationTerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.freeEnergy_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.convexityWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.coercivityWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field FreeEnergyFunctional.lowerSemicontinuityWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field WassersteinGradientFlow.dissipativeFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field WassersteinGradientFlow.freeEnergyDecay` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field WassersteinGradientFlow.jkoCompatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field JKOTimeStep.objective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field JKOTimeStep.stepSize_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field JKOTimeStep.minimizing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field EquilibriumCandidate.reversibleStationary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field EquilibriumCandidate.dissipativeStationary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field EquilibriumCandidate.freeEnergyMinimizer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.reversibleFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.dissipativeFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.totalFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.reversible_part_eq_lieTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.dissipative_part_eq_gradientFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.totalFlow_eq_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `structure-field SouriauMetriplecticOTFlow.entropyProduction_nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L232 [soft] `law-field-locker` in `structure-field MetricTransportCompatibility.compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field LogRadonNikodymHamiltonian.logRN_definition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field LogRadonNikodymHamiltonian.relativeModularHamiltonian_definition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field RelativeEntropyReadout.expectationWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [soft] `law-field-locker` in `structure-field RelativeEntropyReadout.relativeEntropy_eq_expectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L257 [soft] `law-field-locker` in `structure-field JacobianPotentialReadout.additiveCorrection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L263 [soft] `law-field-locker` in `structure-field ModularHamiltonianQuantum.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [soft] `law-field-locker` in `structure-field ModularHamiltonianQuantum.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [soft] `law-field-locker` in `structure-field ModularHamiltonianQuantum.normalizedState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L266 [soft] `law-field-locker` in `structure-field ModularHamiltonianQuantum.modularHamiltonian_definition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field ModularHamiltonianQuantum.normalizedState_definition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [soft] `law-field-locker` in `structure-field DuhamelOperatorDerivativeWitness.operatorDerivative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L274 [soft] `law-field-locker` in `structure-field DuhamelOperatorDerivativeWitness.duhamelFormula` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L275 [soft] `law-field-locker` in `structure-field DuhamelOperatorDerivativeWitness.higherOrderedSimplexWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field RenyiModularDeformation.mellinWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [soft] `law-field-locker` in `structure-field RenyiModularDeformation.petzWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L286 [soft] `law-field-locker` in `structure-field RenyiModularDeformation.sandwichedWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field OperatorialLogPotentialLayer.thermodynamicForce` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `law-field-locker` in `structure-field OperatorialLogPotentialLayer.force_as_relativeModularGradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [advisory] `existential-packaging` in `structure FiniteSouriauMetriplecticOTBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L309 [soft] `law-field-locker` in `structure-field FiniteSouriauMetriplecticOTBridge.metriplectic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

