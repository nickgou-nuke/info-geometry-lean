import InfoGeometry.Physics.Thermodynamics.ChiralChemicalPotentialDeformation

/-!
# Spectral-invariant consequences of the chiral similarity deformation

The chemical-potential Dirac block is a conjugation by the explicit diagonal
factor `gibbsFactor μ`.  This owner records the finite algebraic consequence
that is available without invoking a spectral theorem: the conjugating factors
are two-sided inverses and cyclic matrix traces are unchanged.

Characteristic-polynomial and projector transport statements remain separate
specializations requiring their own finite-dimensional hypotheses.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics
open InfoGeometry.Physics.Thermodynamics

noncomputable section

theorem chemicalPotentialDiracFlow_conjugation (μ Δ : ℝ) :
    chemicalPotentialDiracFlow μ Δ =
      gibbsFactor μ * diracOperator Δ * gibbsFactor (-μ) := by
  rfl

theorem chemicalPotentialDiracFlow_conjugating_factors_left (μ : ℝ) :
    gibbsFactor (-μ) * gibbsFactor μ = (1 : BdGBlock ℝ) := by
  exact gibbsFactor_neg_mul μ

theorem chemicalPotentialDiracFlow_conjugating_factors_right (μ : ℝ) :
    gibbsFactor μ * gibbsFactor (-μ) = (1 : BdGBlock ℝ) := by
  exact gibbsFactor_inv μ

/-- The ordinary finite matrix trace is invariant under the chemical-potential
similarity deformation. -/
theorem chemicalPotentialDiracFlow_trace_eq (μ Δ : ℝ) :
    Matrix.trace (chemicalPotentialDiracFlow μ Δ) =
      Matrix.trace (diracOperator Δ) := by
  rw [chemicalPotentialDiracFlow_conjugation]
  rw [Matrix.trace_mul_cycle]
  rw [chemicalPotentialDiracFlow_conjugating_factors_left]
  simp

end

end InfoGeometry.Canonical
