import InfoGeometry.Topology.CantorBoundaryRealClockShift

/-!
Algebraic dependency order: the first-order equation and the phase square,
together with a specified commutation law, imply the second-order equation.
The Cuntz branch difference below uses the existing real boundary operators.
Neither a Klein seam nor a positive spectral gap is assumed or derived here.
-/

namespace InfoGeometry.Synthesis.CuntzKleinPropagation

section Ring

variable {A : Type*} [Ring A]

theorem square_equation_of_anticommute
    (difference coefficient state phase : A)
    (phase_square : phase * phase = -1)
    (anticommutes : difference * coefficient = -(coefficient * difference))
    (equation : difference * state = coefficient * state * phase) :
    difference * difference * state = coefficient * coefficient * state := by
  calc
    difference * difference * state = difference * (difference * state) :=
      mul_assoc _ _ _
    _ = difference * (coefficient * state * phase) := by rw [equation]
    _ = (difference * coefficient) * state * phase := by simp only [mul_assoc]
    _ = -(coefficient * (difference * state) * phase) := by
      rw [anticommutes]
      simp only [neg_mul, mul_assoc]
    _ = -(coefficient * (coefficient * state * phase) * phase) := by rw [equation]
    _ = -((coefficient * coefficient * state) * (phase * phase)) := by
      simp only [mul_assoc]
    _ = coefficient * coefficient * state := by rw [phase_square]; simp

theorem square_equation_of_commute
    (difference coefficient state phase : A)
    (phase_square : phase * phase = -1)
    (commutes : Commute difference coefficient)
    (equation : difference * state = coefficient * state * phase) :
    difference * difference * state = -(coefficient * coefficient * state) := by
  calc
    difference * difference * state = difference * (difference * state) :=
      mul_assoc _ _ _
    _ = difference * (coefficient * state * phase) := by rw [equation]
    _ = (difference * coefficient) * state * phase := by simp only [mul_assoc]
    _ = coefficient * (difference * state) * phase := by
      rw [commutes.eq]
      simp only [mul_assoc]
    _ = coefficient * (coefficient * state * phase) * phase := by rw [equation]
    _ = (coefficient * coefficient * state) * (phase * phase) := by
      simp only [mul_assoc]
    _ = -(coefficient * coefficient * state) := by rw [phase_square]; simp

end Ring

section Boundary

open InfoGeometry.Topology.CantorBoundaryCuntzO2

noncomputable def branchDifference : BoundaryOperator ℝ := S 0 - S 1

theorem first_branch_readout : T 0 * branchDifference = 1 := by
  simp [branchDifference, mul_sub, ortho]

theorem second_branch_readout : T 1 * branchDifference = -1 := by
  simp [branchDifference, mul_sub, ortho]

theorem branch_square_equation
    (coefficient state phase : BoundaryOperator ℝ)
    (phase_square : phase * phase = -1)
    (anticommutes : branchDifference * coefficient = -(coefficient * branchDifference))
    (equation : branchDifference * state = coefficient * state * phase) :
    branchDifference * branchDifference * state = coefficient * coefficient * state :=
  square_equation_of_anticommute _ _ _ _ phase_square anticommutes equation

end Boundary

end InfoGeometry.Synthesis.CuntzKleinPropagation
