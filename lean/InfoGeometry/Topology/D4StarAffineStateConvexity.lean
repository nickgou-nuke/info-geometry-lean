import InfoGeometry.Topology.D4StarFiniteAffineState
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Convex mixing of the finite two-class affine states. -/

def mixBooleanAffineStates
    (weight : ℚ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (s t : BooleanAffineState) : BooleanAffineState :=
  ⟨(weight * s.centreWeight + (1 - weight) * t.centreWeight,
      weight * s.outerWeight + (1 - weight) * t.outerWeight), by
    constructor
    · exact add_nonneg
        (mul_nonneg hweight0 s.centre_nonneg)
        (mul_nonneg (sub_nonneg.mpr hweight1) t.centre_nonneg)
    · constructor
      · exact add_nonneg
          (mul_nonneg hweight0 s.outer_nonneg)
          (mul_nonneg (sub_nonneg.mpr hweight1) t.outer_nonneg)
      · rw [show weight * s.centreWeight + (1 - weight) * t.centreWeight +
            (weight * s.outerWeight + (1 - weight) * t.outerWeight) =
            weight * (s.centreWeight + s.outerWeight) +
              (1 - weight) * (t.centreWeight + t.outerWeight) by ring]
        rw [s.normalized, t.normalized]
        ring⟩

theorem affineExpectation_mix
    (weight : ℚ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (s t : BooleanAffineState) (f : C(D4StarQuotient, ℚ)) :
    affineExpectation (mixBooleanAffineStates weight hweight0 hweight1 s t) f =
      weight * affineExpectation s f +
        (1 - weight) * affineExpectation t f := by
  dsimp [affineExpectation, mixBooleanAffineStates]
  ring

end InfoGeometry.Topology.PauliJungD4Star
