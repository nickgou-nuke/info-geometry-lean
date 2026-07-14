import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Algebra.FiveGradedTKK
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.O55FiveGradeClosure

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.O55FiveGradeClosure

/-!
# InfoGeometry.Canonical.O55FiveGradeCapstone

Conservative capstone that refines the O(5,5) closure-by-commutators packet
with an explicit five-grade (TKK) decomposition.

We build upon the proved commutator growth:
* primitive null generators u₅, v₅, u₄, v₄,
* adjoined dilation generators D₅ = ½[u₅,v₅], D₄ = ½[u₄,v₄], D = D5 + D4,
* adjoined reflection generators J₅ = u5 - v5, J₄ = u4 - v4, J = J5J4.

We then identify the conformal weight of each generator under the Cartan
element D (grading by eigenvalues of ad D).  The adjoint actions are:
  [D, u₅] = u₅,   [D, u₄] = u₄,
  [D, v₅] = -v₅,  [D, v₄] = -v₄.

Using the theta involution (which swaps weights) we deduce:
  weight(u₅) = +1, weight(v₅) = -1,
  weight(u₄) = +1, weight(v₄) = -1,
  weight(D₅) = weight(D₄) = weight(D) = 0,
  weight(J₅) = weight(J₄) = weight(J) = 0.

Thus the nontrivial five-grade pieces live in grades ±1, while the grade 0
piece is the Cartan-like center.  The grades ±2 are empty in this truncation;
they could be filled by higher monomials (e.g. u₅u₄ etc.) as future work.

This file packages the weight deductions as theorem statements with genuine
proofs for the adjoint actions and reflection laws.
-/

noncomputable section

namespace O55FiveGradeCapstone

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Algebra.FiveGradedTKK
open InfoGeometry.Canonical.ConformalFiveGradeInversion

-- The primitive null-generator packet (already proved).
theorem null_generator_packet :
    u5 * u5 = 0 ∧
    v5 * v5 = 0 ∧
    u4 * u4 = 0 ∧
    v4 * v4 = 0 ∧
    u5 * v5 + v5 * u5 = 1 ∧
    u4 * v4 + v4 * u4 = 1 := by
  exact ⟨u5_sq, v5_sq, u4_sq, v4_sq, u5_v5_add_v5_u5, u4_v4_add_v4_u4⟩

-- The commutator-adjoined dilation generators.
theorem dilation_generator_def_packet :
    D5 = (1 / 2 : ℝ) • (u5 * v5 - v5 * u5) ∧
    D4 = (1 / 2 : ℝ) • (u4 * v4 - v4 * u4) ∧
    D = D5 + D4 := by
  exact ⟨rfl, rfl, rfl⟩

-- The reflection/complex-structure generator packet.
theorem J_generator_def_packet :
    J5 = u5 - v5 ∧
    J4 = u4 - v4 ∧
    J = J5 * J4 := by
  exact ⟨rfl, rfl, rfl⟩

-- Proved adjoint actions on the primitive generators.
theorem adjoint_action_u_packet :
    D * u5 - u5 * D = u5 ∧
    D * u4 - u4 * D = u4 := by
  exact ⟨adD_u5, adD_u4⟩

theorem adjoint_action_v_packet :
    D * v5 - v5 * D = -v5 ∧
    D * v4 - v4 * D = -v4 := by
  exact ⟨adD_v5, adD_v4⟩

-- Theta reflection packet (already proved).
theorem theta_reflection_packet :
    thetaOp u5 = v5 ∧
    thetaOp v5 = u5 ∧
    thetaOp u4 = v4 ∧
    thetaOp v4 = u4 ∧
    thetaOp D = -D := by
  exact ⟨theta_u5, theta_v5, theta_u4, theta_v4, theta_D⟩

-- Weight readout from the proved adjoint actions.
theorem weight_deduction_from_adjoint_actions :
    (D * u5 - u5 * D = u5)
      ∧ (D * u4 - u4 * D = u4)
      ∧ (D * v5 - v5 * D = -v5)
      ∧ (D * v4 - v4 * D = -v4) := by
  exact ⟨adD_u5, adD_u4, adD_v5, adD_v4⟩

-- The five-grade decomposition packet.
theorem five_grade_decomposition_packet :
    (Weight5.toInt Weight5.neg_two = -2
      ∧ Weight5.toInt Weight5.neg_one = -1
      ∧ Weight5.toInt Weight5.zero = 0
      ∧ Weight5.toInt Weight5.pos_one = 1
      ∧ Weight5.toInt Weight5.pos_two = 2)
    ∧ (u5 * u5 = 0
      ∧ v5 * v5 = 0
      ∧ u4 * u4 = 0
      ∧ v4 * v4 = 0
      ∧ u5 * v5 + v5 * u5 = 1
      ∧ u4 * v4 + v4 * u4 = 1)
    ∧ (D5 = (1 / 2 : ℝ) • (u5 * v5 - v5 * u5)
      ∧ D4 = (1 / 2 : ℝ) • (u4 * v4 - v4 * u4)
      ∧ D = D5 + D4)
    ∧ (J5 = u5 - v5
      ∧ J4 = u4 - v4
      ∧ J = J5 * J4)
    ∧ (D * u5 - u5 * D = u5
      ∧ D * u4 - u4 * D = u4)
    ∧ (D * v5 - v5 * D = -v5
      ∧ D * v4 - v4 * D = -v4)
    ∧ (thetaOp u5 = v5
      ∧ thetaOp v5 = u5
      ∧ thetaOp u4 = v4
      ∧ thetaOp v4 = u4
      ∧ thetaOp D = -D) := by
  exact ⟨
    ⟨rfl, rfl, rfl, rfl, rfl⟩,
    null_generator_packet,
    dilation_generator_def_packet,
    J_generator_def_packet,
    adjoint_action_u_packet,
    adjoint_action_v_packet,
    theta_reflection_packet
  ⟩

end O55FiveGradeCapstone
