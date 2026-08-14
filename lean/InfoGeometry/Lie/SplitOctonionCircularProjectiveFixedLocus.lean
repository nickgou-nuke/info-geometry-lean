import InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow
import InfoGeometry.Twistor.ProjectiveNullPolarIncidence

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionCircularProjectiveFixedLocus

open InfoGeometry.Lie.SplitOctonionCircularProjectiveNullBoundary
open InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow
open InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge
open InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence

abbrev Coord := Fin 8 → ℝ
abbrev CircularNullBoundary := TwistorSpace circularPeirceQuadratic

def zeroWeightSubmodule : Submodule ℝ Coord :=
  Submodule.span ℝ {Pi.single 0 1, Pi.single 4 1}

def positiveWeightSubmodule : Submodule ℝ Coord :=
  Submodule.span ℝ {Pi.single 1 1, Pi.single 2 1, Pi.single 3 1}

def negativeWeightSubmodule : Submodule ℝ Coord :=
  Submodule.span ℝ {Pi.single 5 1, Pi.single 6 1, Pi.single 7 1}

theorem hyperbolicFlow_on_zeroWeight (t : ℝ) (x : Coord) (hx : x ∈ zeroWeightSubmodule) :
    hyperbolicFlowCoordinate t x = x := by
  sorry

theorem hyperbolicFlow_on_positiveWeight (t : ℝ) (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp t • x := by
  sorry

theorem hyperbolicFlow_on_negativeWeight (t : ℝ) (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    hyperbolicFlowCoordinate t x = Real.exp (-t) • x := by
  sorry

theorem positiveWeight_totallyNull (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  sorry

theorem negativeWeight_totallyNull (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  sorry

theorem projective_positiveWeight_fixed (t : ℝ) (x : Coord) (hx_ne : x ≠ 0)
    (hx : x ∈ positiveWeightSubmodule) :
    circularNullBoundaryFlow t (twistorMk circularPeirceQuadratic x hx_ne (positiveWeight_totallyNull x hx)) =
      twistorMk circularPeirceQuadratic x hx_ne (positiveWeight_totallyNull x hx) := by
  sorry

theorem projective_negativeWeight_fixed (t : ℝ) (x : Coord) (hx_ne : x ≠ 0)
    (hx : x ∈ negativeWeightSubmodule) :
    circularNullBoundaryFlow t (twistorMk circularPeirceQuadratic x hx_ne (negativeWeight_totallyNull x hx)) =
      twistorMk circularPeirceQuadratic x hx_ne (negativeWeight_totallyNull x hx) := by
  sorry

theorem zeroWeight_null_iff (x : Coord) (hx : x ∈ zeroWeightSubmodule) :
    circularPeirceQuadratic x = 0 ↔ (x 0 = 0 ∨ x 4 = 0) := by
  sorry

theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero (t : ℝ) (ht : t ≠ 0)
    (p : CircularNullBoundary) :
    circularNullBoundaryFlow t p = p ↔
      (p.1.rep ∈ positiveWeightSubmodule ∨
       p.1.rep ∈ negativeWeightSubmodule ∨
       (p.1.rep ∈ zeroWeightSubmodule ∧ (p.1.rep 0 = 0 ∨ p.1.rep 4 = 0))) := by
  sorry

theorem circularNullBoundaryFlow_preserves_incidence (t : ℝ) (p q : CircularNullBoundary) :
    NullPolarIncident circularPeirceQuadratic (circularNullBoundaryFlow t p) (circularNullBoundaryFlow t q) ↔
      NullPolarIncident circularPeirceQuadratic p q := by
  sorry

end InfoGeometry.Lie.SplitOctonionCircularProjectiveFixedLocus
