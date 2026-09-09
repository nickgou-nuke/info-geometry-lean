import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.HolographicEmergence
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.DeepHorizon

Canonical facade for the deep-horizon synthesis:

- grand-canonical expert routing and split-Clifford mode lifts
- Cayley transport invariance in dual-flat geometry
- Tomita-Takesaki modular atom realization in split `Cl(1,1)`
- holographic emergence package (time flow, anomaly-scale, torsion, twistor closure)
-/

namespace InfoGeometry.Canonical.DeepHorizon

export InfoGeometry.Canonical.MoE (
  exists_perm_decomposition_of_bistochastic
  exists_perm_decomposition_of_sinkhornBalanced
  SplitCliffordSuperData
  modeDiracOperator
  diracEulerStep
  exists_modewiseClifford_rep_of_bistochastic
)

export InfoGeometry.Canonical.Cayley (
  CayleyBridge
  CayleyCompatibleDualFlat
  cayleyPythagoreanInvariance
)

export InfoGeometry.Canonical.TomitaTakesaki (
  cptAtoms_generate_splitCliffordAlg
  DiagonalPositiveTimeVector
  PositiveTimeVector
  modularConjugationJ
  modularSignEpsilon
  modularComplexI
  modularSignAdditiveModularFlow
  modularAtomRepresentation
  tomitaRepresentation
)

export InfoGeometry.Krein (
  modular_j
  spectral_epsilon
  complex_i
)

export InfoGeometry.Canonical.HolographicEmergence (
  EmergentTimeFlow
  emergentTimeFlow_of_sinkhornTrajectory
  anomalyScalePhase_of_nonzeroAnomaly
  pathDependence_of_twistedInference
  exists_gaugeOrderHysteresis
)

end InfoGeometry.Canonical.DeepHorizon
