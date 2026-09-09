import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat

/-!
# Coordinate form of the normalized-trace colimit bridge

The normalized trace is the distinguished compatible-family point.  This
owner states its agreement with the topological colimit readout through the
coordinate `TopCat` morphisms exposed by the preceding owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCatBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine

theorem normalizedTrace_coordinate_eq
    (n : ℕ) :
    coordinateTopCatHom n normalizedTraceReadoutFamily =
      LinearMap.toContinuousLinearMap (normalizedTraceLinear n) := by
  rfl

theorem normalizedTraceColimitMap_matches_coordinate
    (n : ℕ) (A : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (topologicalInjection n A) =
      coordinateTopCatHom n normalizedTraceReadoutFamily A := by
  exact normalizedTraceColimitMap_matches_inverse_family n A

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCatBridge
