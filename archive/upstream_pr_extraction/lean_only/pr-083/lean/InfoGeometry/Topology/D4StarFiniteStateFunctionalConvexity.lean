import InfoGeometry.Topology.D4StarFiniteStateFunctional

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

theorem affineStateFunctional_mix
    (weight : ℚ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (s t : BooleanAffineState) (f : C(D4StarQuotient, ℚ)) :
    affineStateFunctional
      (mixBooleanAffineStates weight hweight0 hweight1 s t) f =
      weight * affineStateFunctional s f +
        (1 - weight) * affineStateFunctional t f := by
  exact affineExpectation_mix weight hweight0 hweight1 s t f

theorem uniformFunctional_is_normalized :
    FiniteStateFunctional.IsNormalized
      (affineStateFunctional uniformBooleanAffineState) :=
  affineStateFunctional_isNormalized uniformBooleanAffineState

theorem uniformFunctional_is_positive :
    FiniteStateFunctional.IsPositive
      (affineStateFunctional uniformBooleanAffineState) := by
  exact affineStateFunctional_isPositive uniformBooleanAffineState

end InfoGeometry.Topology.PauliJungD4Star
