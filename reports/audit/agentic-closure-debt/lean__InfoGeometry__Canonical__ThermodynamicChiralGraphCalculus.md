# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:05.456104+00:00`
Root: `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **89**
- Hard: **0**
- Soft: **80**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean` | `advisory` | 169 | 0 | 80 | 9 | 89 |

## Findings by file

### `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean`
- module: `InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus`
- status: `advisory`
- debt_score: `169`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `local-hypothesis-injection` in `theorem irreversibleFluxAffinity_nonneg_of_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L37 [advisory] `local-hypothesis-injection` in `theorem irreversibleFluxAffinity_nonneg_of_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L38 [advisory] `local-hypothesis-injection` in `theorem irreversibleFluxAffinity_nonneg_of_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L63 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.src` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.dst` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.forwardRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.reverseRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.conductance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.bias` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.capacity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.probability` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field DirectedThermoGraph.affinity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [soft] `simp-law-injection` in `simp-declaration detailedBalanceOnCycle_iff_wilsonLoop_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L114 [soft] `simp-law-injection` in `simp-declaration chiralDriveOnCycle_iff_wilsonLoop_ne_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [soft] `simp-law-injection` in `simp-declaration stochasticCurrent_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `simp-law-injection` in `simp-declaration circuitCurrent_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `simp-law-injection` in `simp-declaration storedCharge_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration logAffinity_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [soft] `simp-law-injection` in `simp-declaration cycleCurvatureLog_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L170 [soft] `simp-law-injection` in `simp-declaration stochasticAffinity_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `simp-law-injection` in `simp-declaration gaugeCoboundary_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L215 [soft] `simp-law-injection` in `simp-declaration gaugeBoundaryTerm_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [soft] `simp-law-injection` in `simp-declaration gaugeShiftedLogAffinity_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L223 [soft] `simp-law-injection` in `simp-declaration gaugeShiftedCycleCurvatureLog_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L229 [soft] `skeletal-proof` in `theorem gaugeShiftedCycleCurvatureLog_eq_cycleCurvatureLog_add_boundary` — proof appears to close via minimal tactic one-liner
  - L268 [soft] `skeletal-proof` in `theorem cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary` — proof appears to close via minimal tactic one-liner
  - L306 [soft] `law-field-locker` in `structure-field LogWilsonCycleLaw.detailedBalance_iff_zero_log_curvature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [advisory] `existential-packaging` in `def IsGradientFlow` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L355 [soft] `simp-law-injection` in `simp-declaration incidenceMap_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L371 [soft] `law-field-locker` in `structure-field SchnakenbergDecomposition.gradientPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [soft] `law-field-locker` in `structure-field SchnakenbergDecomposition.cyclePart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L375 [soft] `law-field-locker` in `structure-field SchnakenbergDecomposition.reconstruct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field SchnakenbergDecomposition.unique` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L379 [advisory] `existential-packaging` in `theorem schnakenberg_decomposition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L412 [soft] `law-field-locker` in `structure-field DrivenThermoGraph.graphAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [advisory] `existential-packaging` in `structure DrivenThermoGraph.BarrierDrivenGraph` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L423 [soft] `law-field-locker` in `structure-field DrivenThermoGraph.BarrierDrivenGraph.gaugeClosed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L424 [soft] `law-field-locker` in `structure-field DrivenThermoGraph.BarrierDrivenGraph.exactConnection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L469 [soft] `simp-law-injection` in `simp-declaration timeReversedGraph_forwardRate` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L473 [soft] `simp-law-injection` in `simp-declaration timeReversedGraph_reverseRate` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L477 [soft] `simp-law-injection` in `simp-declaration pathEntropyProduction_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L481 [soft] `skeletal-proof` in `theorem pathForwardBackwardRatio_eq_exp_pathEntropyProduction` — proof appears to close via minimal tactic one-liner
  - L501 [soft] `law-field-locker` in `structure-field IntegralFluctuationLaw.entropyProduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field IntegralFluctuationLaw.expectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L503 [soft] `law-field-locker` in `structure-field IntegralFluctuationLaw.exp_neg_entropy_expectation_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L515 [soft] `law-field-locker` in `structure-field PathProbabilityRatioLaw.forwardProbability` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L516 [soft] `law-field-locker` in `structure-field PathProbabilityRatioLaw.backwardProbability` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L517 [soft] `law-field-locker` in `structure-field PathProbabilityRatioLaw.entropyProduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L518 [soft] `law-field-locker` in `structure-field PathProbabilityRatioLaw.ratio_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L533 [soft] `skeletal-proof` in `theorem wilsonLoop_eq_exp_cycleCurvatureLog` — proof appears to close via minimal tactic one-liner
  - L602 [soft] `law-field-locker` in `structure-field KirchhoffConservation.chargeRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L603 [soft] `law-field-locker` in `structure-field KirchhoffConservation.conservation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L612 [soft] `law-field-locker` in `structure-field EntropyProductionNonneg.pointwise_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L613 [soft] `law-field-locker` in `structure-field EntropyProductionNonneg.total_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L614 [soft] `skeletal-proof` in `theorem entropyProduction_nonneg_of_pointwise` — proof appears to close via minimal tactic one-liner
  - L621 [soft] `skeletal-proof` in `theorem stochasticCurrent_mul_stochasticAffinity_nonneg_of_positive_flux` — proof appears to close via minimal tactic one-liner
  - L634 [soft] `skeletal-proof` in `theorem stochasticEntropyProduction_nonneg_of_positive_flux` — proof appears to close via minimal tactic one-liner
  - L718 [soft] `law-field-locker` in `structure-field EquilibriumExistenceUniqueness.distribution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L720 [soft] `law-field-locker` in `structure-field EquilibriumExistenceUniqueness.unique` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L721 [advisory] `existential-packaging` in `theorem existsUnique_equilibriumDistribution` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L754 [soft] `simp-law-injection` in `simp-declaration wilsonLoop_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L759 [soft] `simp-law-injection` in `simp-declaration logCurvature_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L774 [soft] `simp-law-injection` in `simp-declaration detailedBalance_iff_wilsonLoop_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L778 [soft] `simp-law-injection` in `simp-declaration chiralDrive_iff_wilsonLoop_ne_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L782 [soft] `simp-law-injection` in `simp-declaration not_chiralDrive_of_detailedBalance` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L831 [soft] `skeletal-proof` in `theorem graph_wilsonLoop_eq_triangle` — proof appears to close via minimal tactic one-liner
  - L838 [soft] `skeletal-proof` in `theorem detailedBalance_iff_graph_cycle_ratio_product_eq_one` — proof appears to close via minimal tactic one-liner
  - L874 [soft] `law-field-locker` in `structure-field ThermodynamicGraphLambdaPacket.semanticInterpretation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L875 [soft] `law-field-locker` in `structure-field ThermodynamicGraphLambdaPacket.linearResourceDiscipline` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L876 [soft] `law-field-locker` in `structure-field ThermodynamicGraphLambdaPacket.probabilisticSemantics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L877 [soft] `law-field-locker` in `structure-field ThermodynamicGraphLambdaPacket.circuitSemantics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L878 [soft] `law-field-locker` in `structure-field ThermodynamicGraphLambdaPacket.wilsonLoopSemantics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L886 [soft] `simp-law-injection` in `simp-declaration semanticInterpretation_valid` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L890 [soft] `simp-law-injection` in `simp-declaration linearResourceDiscipline_valid` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L894 [soft] `simp-law-injection` in `simp-declaration probabilisticSemantics_valid` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L898 [soft] `simp-law-injection` in `simp-declaration circuitSemantics_valid` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L902 [soft] `simp-law-injection` in `simp-declaration wilsonLoopSemantics_valid` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L946 [soft] `law-field-locker` in `structure-field DeBruijnEdge.shift_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L951 [soft] `law-field-locker` in `structure-field DecoratedDeBruijnGraph.forwardRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L952 [soft] `law-field-locker` in `structure-field DecoratedDeBruijnGraph.reverseRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1003 [soft] `law-field-locker` in `structure-field NonlinearCost.erasure_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1004 [soft] `law-field-locker` in `structure-field NonlinearCost.duplication_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1069 [advisory] `existential-packaging` in `def IsNormal` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1080 [soft] `law-field-locker` in `structure-field PortSignature.openPort` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1112 [soft] `law-field-locker` in `structure-field TracePortSemantics.portsOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1113 [soft] `law-field-locker` in `structure-field TracePortSemantics.trace_ports` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

