import InfoGeometry.Physics.Cl55BranchingSynthesis
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Duality and five-grade channel squares

This file packages the grade-reversing part of the five-grade architecture.
The reversal is deliberately supplied as a linear map together with its
grade and bracket compatibility laws.  Thus the results below are genuine
consequences of a concrete representation contract; they do not identify a
Zorn operator carrier with an abstract `FiveGrading` without such a contract.
-/

namespace InfoGeometry.Physics.Cl55FiveGradeDualityBridge

open InfoGeometry.Physics.Algebra
open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

noncomputable section

variable {L : Type*} [AddCommGroup L] [Module ℝ L]
  [LieRing L] [LieAlgebra ℝ L]

/-- A bracket-compatible grade reversal for a five-graded Lie algebra. -/
structure GradeReversal (G : FiveGrading L) where
  theta : L →ₗ[ℝ] L
  negOne_of_posOne : ∀ {x : L}, x ∈ G.gPosOne → theta x ∈ G.gNegOne
  posOne_of_negOne : ∀ {x : L}, x ∈ G.gNegOne → theta x ∈ G.gPosOne
  negTwo_of_posTwo : ∀ {x : L}, x ∈ G.gPosTwo → theta x ∈ G.gNegTwo
  posTwo_of_negTwo : ∀ {x : L}, x ∈ G.gNegTwo → theta x ∈ G.gPosTwo
  zero_of_zero : ∀ {x : L}, x ∈ G.gZero → theta x ∈ G.gZero
  map_bracket : ∀ x y : L, theta ⁅x, y⁆ = ⁅theta x, theta y⁆

namespace GradeReversal

variable {G : FiveGrading L} (R : GradeReversal G)

/-- Same-grade positive brackets are transported to the negative grade-two
sector.  This is the left square of the grade-reversal diagram. -/
theorem positive_bracket_to_negative
    {x y : L} (hx : x ∈ G.gPosOne) (hy : y ∈ G.gPosOne) :
    R.theta ⁅x, y⁆ ∈ G.gNegTwo := by
  rw [R.map_bracket]
  exact G.bracket_neg_one_neg_one _ _
    (R.negOne_of_posOne hx) (R.negOne_of_posOne hy)

/-- Same-grade negative brackets are transported to the positive grade-two
sector. -/
theorem negative_bracket_to_positive
    {x y : L} (hx : x ∈ G.gNegOne) (hy : y ∈ G.gNegOne) :
    R.theta ⁅x, y⁆ ∈ G.gPosTwo := by
  rw [R.map_bracket]
  exact G.bracket_pos_one_pos_one _ _
    (R.posOne_of_negOne hx) (R.posOne_of_negOne hy)

/-- The complete duality channel packet. -/
theorem channel_square
    {xNeg yNeg xPos yPos : L}
    (hxNeg : xNeg ∈ G.gNegOne) (hyNeg : yNeg ∈ G.gNegOne)
    (hxPos : xPos ∈ G.gPosOne) (hyPos : yPos ∈ G.gPosOne) :
    ⁅xNeg, yNeg⁆ ∈ G.gNegTwo ∧
      ⁅xPos, yPos⁆ ∈ G.gPosTwo ∧
      R.theta ⁅xPos, yPos⁆ ∈ G.gNegTwo ∧
      R.theta ⁅xNeg, yNeg⁆ ∈ G.gPosTwo := by
  exact ⟨G.bracket_neg_one_neg_one _ _ hxNeg hyNeg,
    G.bracket_pos_one_pos_one _ _ hxPos hyPos,
    R.positive_bracket_to_negative hxPos hyPos,
    R.negative_bracket_to_positive hxNeg hyNeg⟩

/-- Master channel packet: the two same-grade outputs, the opposite-grade
mixed output, and the grade-reversed image of each same-grade channel. -/
theorem full_channel_packet
    {xNeg yNeg xPos yPos : L}
    (hxNeg : xNeg ∈ G.gNegOne) (hyNeg : yNeg ∈ G.gNegOne)
    (hxPos : xPos ∈ G.gPosOne) (hyPos : yPos ∈ G.gPosOne) :
    ⁅xNeg, yNeg⁆ ∈ G.gNegTwo ∧
      ⁅xPos, yPos⁆ ∈ G.gPosTwo ∧
      ⁅xNeg, yPos⁆ ∈ G.gZero ∧
      R.theta ⁅xPos, yPos⁆ ∈ G.gNegTwo ∧
      R.theta ⁅xNeg, yNeg⁆ ∈ G.gPosTwo := by
  exact ⟨G.bracket_neg_one_neg_one _ _ hxNeg hyNeg,
    G.bracket_pos_one_pos_one _ _ hxPos hyPos,
    G.bracket_neg_one_pos_one _ _ hxNeg hyPos,
    R.positive_bracket_to_negative hxPos hyPos,
    R.negative_bracket_to_positive hxNeg hyNeg⟩

/-! ## Direct naturality readouts

The weak `GradeReversal` contract already contains the commuting square as
`map_bracket`.  These named corollaries expose the three graded channels
directly, so downstream realization owners do not need to unfold the
structure field themselves.
-/

theorem positive_channel_commutes
    {x y : L} (hx : x ∈ G.gPosOne) (hy : y ∈ G.gPosOne) :
    R.theta ⁅x, y⁆ = ⁅R.theta x, R.theta y⁆ :=
  R.map_bracket x y

theorem negative_channel_commutes
    {x y : L} (hx : x ∈ G.gNegOne) (hy : y ∈ G.gNegOne) :
    R.theta ⁅x, y⁆ = ⁅R.theta x, R.theta y⁆ :=
  R.map_bracket x y

theorem mixed_channel_commutes
    {x : L} (hx : x ∈ G.gNegOne) {y : L} (hy : y ∈ G.gPosOne) :
    R.theta ⁅x, y⁆ = ⁅R.theta x, R.theta y⁆ :=
  R.map_bracket x y

theorem mixed_bracket_stays_zero
    {xNeg yPos : L}
    (hxNeg : xNeg ∈ G.gNegOne) (hyPos : yPos ∈ G.gPosOne) :
    R.theta ⁅xNeg, yPos⁆ ∈ G.gZero := by
  exact R.zero_of_zero (G.bracket_neg_one_pos_one _ _ hxNeg hyPos)

end GradeReversal

end
end InfoGeometry.Physics.Cl55FiveGradeDualityBridge
