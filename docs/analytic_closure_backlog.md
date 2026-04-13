# Analytic Closure Backlog

This note is a live backlog sketch for the current repository state.

It is not an authority file and it is not a completeness certificate. It exists
to record the shortest remaining theorem paths after the corrected phase-space
owner and generalized-metric algebra were made real.

## Snapshot: `9d81730` Fixed Points

This snapshot materially strengthens the operator spine, but it is not yet
uniformly kernel-closed.

### Settled Improvements

- Drazin lane now has a compiled existence backbone:
  - `lean/InfoGeometry/Singular/Drazin.lean` (`exists_drazinInverse_global`)
  - `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean`
    (`exists_canonicalDrazinInverse_global_endCLM`)
  - `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean`
    (`AscentAtZero`, `DescentAtZero`, finite ascent/descent packaging, Riesz-style packaging)
- Defect-to-gravity bridge is no longer promissory:
  - `lean/InfoGeometry/Canonical/SuperchargeEinsteinSourceBridge.lean`
    now carries explicit compatibility packaging, mismatch-to-obstruction, `chiralScale ≠ 0`,
    and Einstein-source closures (including localized boundary-carrier variants).
- Capstone internalization improved:
  - `lean/InfoGeometry/Canonical/MasterSynthesis.lean` now derives Bott closure
    via `InformationalLichnerowiczBottBridge` from `hCompat`, rather than taking
    a free `LichnerowiczBalancedCl11` witness.
- Tomita/cocycle internalization improved:
  - `lean/InfoGeometry/Canonical/ModularWeldBridge.lean` owns finite `relativeLogDensityOperator`.
  - `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean` and
    `lean/InfoGeometry/Canonical/YangMillsContinuum.lean` add welded flow-unit wrappers
    reducing free cocycle/bridge parameters.
- Representation-lineage corpus is now on the canonical umbrella:
  - `lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean`
  - `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean`
  - `lean/InfoGeometry/Canonical/HeadTrialityCore.lean`
  These are structurally honest owner surfaces, but still early-stage.
- Tooling/process hardening improved:
  replay verification, schema-governed residue packets, statement-lock tightening,
  and isolated Hermes configuration.

### Open Fixtures

- `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean` is still promissory in this snapshot
  (explicit `sorry` placeholders remain in the spectral-isolation-to-Drazin descent lane).
- `lean/InfoGeometry/Canonical/MasterSynthesis.lean` still carries capstone-facing external
  witnesses on top-level synthesis (notably `hEin`, `hAnomalySkew`, `hHelicity`, `Mod`, `hCompat`).
- Representation-lineage theorems are mostly first-step invariants, transports, and
  preservation wrappers; deeper closure results remain to be proved.

### Priority Order (Post-`9d81730`)

1. Close `DrazinSpectralBridge` (eliminate `sorry`; compile spectral zero-isolation descent).
2. Reduce or internalize `hCompat` in `MasterSynthesis` through lower owner bridges.
3. Eliminate `hHelicity` as a top-level external witness.
4. Attack `hEin` elimination only after the above reductions are complete.

This order is intentional: it removes explicit interface debt from the most local
operator lane outward, rather than trying to discharge the highest geometric witness first.

## What is already closed enough

The following packets are no longer the primary bottleneck:

- corrected phase-space owner:
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
- owner-side generalized-metric algebra:
  - `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- owner-to-doubled chirality and realized projector lane:
  - `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
- recomposition transport corridor:
  - `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`
- KKT / conformal causal branch:
  - `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean`
- operator anomaly / QGT frontier:
  - `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
  - `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`

The remaining work is now branch junction closure, not owner invention.

## Current highest-value backlog

### 1. Internalize the tomita identification at the projector junction

Current status:
- the polarized and recomposition junctions now consume the realized
  generalized-metric projector lane directly;
- the final identification to the maintained tomita generalized-metric
  projector is still carried as an explicit hypothesis in the strongest
  corollaries.

Next step:
- prove that identification internally for the canonical junction data used by
  the maintained polarized/recomposition corridor.

This is the cleanest next theorem gap.

### 2. Strengthen the operator-level obstruction theorem package

Current status:
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean` already owns the
  projector commutator / obstruction scalar link;
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` now formalizes the
  lifted Einstein anomaly on the doubled carrier;
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean` already reaches
  the scalar obstruction norm and Weyl holonomy;
- the source-driven operator package is now explicit (`SourceSpineAndWeylEndpoint`).

Next step:
- reduce explicit commutation/identification hypotheses inside the source-driven
  package and keep the weld trunk-internal. (Partially addressed by recent
  dilation-source derivation from projector agreement).

This is now a compression task, not a missing-shape task.

### 3. Attach the count/projective trunk at the polarized carrier

Current status:
- the count/projective trunk is real:
  - `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
  - `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
  - `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean`
- the corrected phase-space trunk is also real.

Next step:
- prove one explicit meeting theorem on the common polarized carrier, instead of
  leaving the trunks merely adjacent.

### 4. Add a twisted end-to-end example

Current status:
- there are concrete example/regression files for recomposition and
  generalized-metric surfaces;
- there is not yet one example that runs through the full current trunk with a
  nonzero `B` twist.

Next step:
- add one finite-dimensional model that computes:
  - owner generalized metric,
  - realized doubled projectors,
  - polarized fixation,
  - recomposition transport/coherence,
  - conformal or Weyl output where feasible.

### 5. Strengthen the Tomita / Bogoliubov branch

Current status:
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
- `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
- `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

already form a real modular corridor.

Next step:
- connect the current corrected owner trunk to this modular branch by explicit
  adjacent bridge theorems, not by high-level prose.

This is closer than KK/index work.
