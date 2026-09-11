import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Potential.Thermo
import InfoGeometry.Canonical.BohmMadelungFisher

/-!
# Cramér-Rao Bound and emergent Heisenberg Uncertainty

This module formalizes the derivation of the Heisenberg Uncertainty Principle from the
classical Cramér-Rao inequality. 

Using the Fisher information representation of momentum variance (`Var(P) = (1/4) * I_F`),
we show that the classical Cramér-Rao bound (`Var(X) * I_F ≥ 1`) directly implies
the quantum uncertainty relation: `Var(X) * Var(P) ≥ 1/4`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CramerRaoUncertainty

/-- The emergent Heisenberg Uncertainty relation from the classical Cramér-Rao bound. -/
theorem heisenberg_from_cramer_rao (VarX VarP I_F : ℝ)
    (h_cramer_rao : VarX * I_F ≥ 1)
    (h_momentum_var : VarP = (1 / 4) * I_F) :
    VarX * VarP ≥ (1 / 4) := by
  rw [h_momentum_var]
  have h_prod : VarX * ((1 / 4) * I_F) = (1 / 4) * (VarX * I_F) := by ring
  rw [h_prod]
  have h_le : (1 / 4 : ℝ) * 1 ≤ (1 / 4 : ℝ) * (VarX * I_F) := by
    apply mul_le_mul_of_nonneg_left
    · exact h_cramer_rao
    · linarith
  linarith

end InfoGeometry.Canonical.CramerRaoUncertainty

end noncomputable section
