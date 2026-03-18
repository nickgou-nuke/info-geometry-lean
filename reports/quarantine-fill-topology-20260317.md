# Quarantine Fill Topology

Date: 2026-03-17

## Purpose

This note maps the highest-leverage quarantined modules to nearby stable modules
and theorems that could plausibly replace their current proof-vacuous or
degenerate scaffolds.

The goal is not to redesign the library again. The goal is to identify the
smallest already-landed "particles" that can fill the existing holes.

## Method

- Start from the quarantine roots with the largest downstream impact.
- Inspect each root's local definitions and theorem surface.
- Look for nearby non-quarantined modules that already provide equivalent or
  stronger content.
- Separate true source problems from modules that look mostly like stale
  quarantine inertia.

## High-Leverage Roots

### 1. `Canonical.PerelmanW`

File:
- `lean/InfoGeometry/Canonical/PerelmanW.lean`

Observed gap:
- The core layer is still organized around `SatisfiesWLaw`, an abstract
  user-supplied dissipation law.
- This makes the monotonicity theorems formally valid but too weak to count as a
  canonical derived bridge.

Nearest stable particles:
- `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`
- `spectralBasepointLogVolume`
- `spinorialScalarCurvature`
- `normalizedKaehlerRicci_beta_eq_neg_spinorial`
- `spinorialScalarCurvature_eq_zero_of_normalized_fixedpoint`

Fill strategy:
- Keep the abstract `SatisfiesWLaw` layer as a generic shell if needed.
- Promote the spinorial section into the real public surface.
- Refactor downstream consumers to depend on the spinorial/Ricci-derived
  theorems, not on arbitrary `diss`.

Assessment:
- Real source problem, but it has nearby stable replacement particles already.

### 2. `Canonical.HeatKernel`

File:
- `lean/InfoGeometry/Canonical/HeatKernel.lean`

Observed gap:
- `a₀`, `a₁`, total scalar curvature, and Einstein-Hilbert action are fixed by
  definitional scalar surrogates:
  `a₁ = -spectralVolume`, `R = 6 * a₁`.

Nearest stable particles:
- `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`
- `spectralBasepointLogVolume`
- `spinorialScalarCurvature`
- `spectralMongeAmpereDensity`
- `mongeAmpereConsistentAtBasepoint`

Fill strategy:
- Replace local `spectralVolume` with the already-landed
  `spectralBasepointLogVolume`.
- Replace local curvature surrogates with wrappers around
  `spinorialScalarCurvature`.
- If the file remains only a notational facade after that, it becomes a likely
  de-quarantine candidate.

Assessment:
- Best geometry-side first repair.

### 3. `Canonical.BeliefDynamics`

File:
- `lean/InfoGeometry/Canonical/BeliefDynamics.lean`

Observed gap:
- `parallelTransportE` is literally identity.
- `parallelTransportM` is identity on chosen coordinates.
- `quantumGeometryOp` is just `metricOp`.

Nearest stable particles:
- `lean/InfoGeometry/Convex/HessianGeometry.lean`
- `HessianGeometry.dualMap`
- `HessianGeometry.metricOp`
- `HessianGeometry.divergence`
- `HessianGeometry.divergence_nonneg`
- `lean/InfoGeometry/Canonical/InformationTorsion.lean`
- `Connection`
- `informationTorsion`
- `IsTorsionFree`

Fill strategy:
- Split safe content from unsafe content.
- Safe today: `radonNikodymOp`, `exponentialTilt`, and any statements that only
  use divergence or metric operators.
- Unsafe today: both transport definitions and any geometric claims built on
  them.

Assessment:
- True source problem with partial salvage potential.

### 4. `Canonical.QFTTDFTLaunchpad`

File:
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean`

Observed gap:
- The manifest still calls this a vacuity-surface module, but the file now looks
  much more like a pure packaging layer over already proved imports.

Nearest stable particles:
- `lean/InfoGeometry/Geometry/LegendreDuality.lean`
- `LegendreInvolutionAssumptions`
- `LegendreConcreteHypotheses`
- `fenchelGap_zero_along_grad_of_fenchelYoung`
- `lean/InfoGeometry/Canonical/RGFlow.lean`
- `isFixedPoint_of_flowInvariant`
- `isFixedPoint_of_modularCliffordFlowInvariant`
- `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean`
- `SinkhornKMSClosure`
- `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
- `grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported`

Fill strategy:
- Audit whether this module is still substantively vacuous, or whether it is now
  just a stable theorem aggregator.
- If the latter, this may be the lowest-cost de-quarantine candidate in the
  entire list.

Assessment:
- Likely stale quarantine inertia, not a deep source defect.

### 5. `Canonical.YangMillsContinuum`

File:
- `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`

Observed gap:
- `ModularRadonNikodymData` stores a scalar `rnDerivative`.
- Derived modular operator and Hamiltonian are scalar multiples of the identity.

Nearest stable particles:
- `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean`
- `modularShift`
- `SatisfiesKMSLike`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `modularConjugationJ`
- `modularComplexI`
- `PositiveTimeVector`
- `lean/InfoGeometry/Krein/DoubledAdjoint.lean`

Fill strategy:
- Move from scalar RN data to actual operator-level modular data.
- Keep the additive-time and derivative theorems if they can be reproved for a
  non-scalar Hamiltonian input.
- Treat the current scalarized structure as a temporary special case, not the
  public endpoint.

Assessment:
- True source problem; not a quick win.

### 6. `Canonical.YangMillsFinite`

File:
- `lean/InfoGeometry/Canonical/YangMillsFinite.lean`

Observed gap:
- The main structure `FiniteYangMillsBridge` stores obligations as fields and
  later projects them out.

Nearest stable particles:
- Internal constructive theorems already in the same file:
  `expectationSeedReflectionPositivity_of_hypotheses`
  `finiteOsterwalderSchraderLayer_of_positiveTimeVector`
  `finiteWightmanReconstructionLayer_of_expectationSeed`
  `spectralGapFromLogDet_pos_of_coercive`
  `obligations_of_expectationSeedFromLogDet`
- Upstream support:
  `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean`
  `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
  `lean/InfoGeometry/Canonical/ChiralRGFlow.lean`

Fill strategy:
- Stop exposing the stored-witness bundle as the primary theorem surface.
- Rebase downstream code onto the constructive theorems already present in the
  module.
- Keep the structure only as a convenience constructor, if at all.

Assessment:
- Real issue, but most filler particles are already inside the file.

### 7. `Prequantum.Connection`

File:
- `lean/InfoGeometry/Prequantum/Connection.lean`

Observed gap:
- The file is materially about scalar gauge scaling, not genuine connection
  geometry.
- Public names like `connectionObservable` and `covariantDerivative` oversell
  what is actually proved.

Nearest stable particles:
- `lean/InfoGeometry/Prequantum/Scaling.lean`
- `PrequantumData.connectionScale`
- `PrequantumData.covariantScale`
- `PrequantumData.GaugeEquivalent`
- `lean/InfoGeometry/Prequantum/Bundle.lean`
- `ProjectivePrequantumBundle`
- `lean/InfoGeometry/Projective/Rays.lean`
- projective-ray quotient infrastructure

Fill strategy:
- Either rename/narrow the file to reflect that it proves only scalar gauge laws,
  or add actual connection data somewhere else and keep this file as a low-level
  gauge-scaling lemma layer.

Assessment:
- Real source mismatch in semantics, but not analytically deep.

## Likely Facades or Stale Quarantine

These look more like downstream wrappers than primary defect sites:

- `Canonical.CountSubstrateBridge`
- `Canonical.DeepHorizon`
- `Canonical.GrandSynthesis`
- `Canonical.RedLine`
- `Canonical.Rosetta`
- `Canonical.WeylInformationGauge`
- `Canonical.OperatorAlgebraBridge`

Special note:
- `Canonical.AQFTOperatorInterface` appears to be the real degeneracy point in
  the AQFT chain, not `QFTTDFTLaunchpad`.
- The concrete trouble there is the first-leg compression model, which is much
  thinner than the surrounding interface names suggest.

Relevant nearby particles:
- `lean/InfoGeometry/Krein/HilbertBridge.lean`
- `lean/InfoGeometry/Krein/DoubledSpace.lean`
- `lean/InfoGeometry/Projective/ProjectiveMap.lean`

## First Repair Candidates

### Best ROI

1. `Canonical.HeatKernel`
- Strong nearest stable replacements already exist in `RicciMongeAmpere`.
- Repairing it also helps `AnomalyInflow` and the holography chain.

2. `Canonical.QFTTDFTLaunchpad`
- This may already be de-quarantine-ready after a focused audit.
- If so, it gives a fast visible win with little theorem engineering.

3. `Canonical.YangMillsFinite`
- The constructive content appears to be mostly present already.
- The task is mainly to stop making the stored witness structure the canonical
  public endpoint.

### Best Long-Term Root

4. `Canonical.PerelmanW`
- High leverage, but likely needs real theorem-surface surgery rather than a
  simple alias cleanup.

## Practical Next Step

If only one module is touched next, the best first pass is:

1. audit `Canonical.QFTTDFTLaunchpad` for stale quarantine status;
2. if it is still truly vacuous, pivot immediately to `Canonical.HeatKernel`;
3. then use `HeatKernel` as the first real root repair in the geometry spine.
