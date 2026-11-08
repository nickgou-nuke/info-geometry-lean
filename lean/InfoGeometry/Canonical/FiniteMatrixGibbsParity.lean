/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import InfoGeometry.Physics.KleinBottleSewingExact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Parity cancellation for the actual positive finite Gibbs density.
Only the Hamiltonian is assumed Hermitian. The weighted Gibbs functional is
not assumed tracial; cancellation concerns observables odd under the chosen
involution that commutes with the Hamiltonian.
-/
namespace InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hamiltonian symmetries commute with its native Gibbs density.
No self-adjointness or involution hypothesis on the symmetry is needed here. -/
theorem gibbsDensity_commutes_of_commute (H Γ : Matrix n n ℂ)
    (hH : H.IsHermitian) (hcomm : Commute H Γ) (β : ℝ) :
    Commute (gibbsDensity H hH β) Γ := by
  rw [gibbsDensity, ← hH.cfc_eq]
  exact hcomm.cfc_real (expWeight β)

/-- A commuting involution preserves the density under the two-sided action. -/
theorem gibbsDensity_parity_invariant (H Γ : Matrix n n ℂ)
    (hH : H.IsHermitian) (hcomm : Commute H Γ) (hΓ : Γ * Γ = 1) (β : ℝ) :
    Γ * gibbsDensity H hH β * Γ = gibbsDensity H hH β := by
  rw [← (gibbsDensity_commutes_of_commute H Γ hH hcomm β).eq,
    mul_assoc, hΓ, mul_one]

/-- Odd observables have zero unnormalized Gibbs expectation. -/
theorem weightedTrace_gibbsDensity_odd_zero (H Γ X : Matrix n n ℂ)
    (hH : H.IsHermitian) (hcomm : Commute H Γ) (hΓ : Γ * Γ = 1)
    (hodd : X * Γ = -(Γ * X)) (β : ℝ) :
    weightedTrace (gibbsDensity H hH β) X = 0 := by
  rw [weightedTrace_apply, Matrix.trace_mul_comm]
  exact InfoGeometry.Physics.KleinBottleSewingExact.trace_mul_eq_zero_of_anticomm_invariance
    X Γ (gibbsDensity H hH β) hΓ hodd
    (gibbsDensity_parity_invariant H Γ hH hcomm hΓ β)

/-- Normalization preserves the odd cancellation in the actual Gibbs state. -/
theorem gibbsFunctional_odd_zero [Nonempty n] (H Γ X : Matrix n n ℂ)
    (hH : H.IsHermitian) (hcomm : Commute H Γ) (hΓ : Γ * Γ = 1)
    (hodd : X * Γ = -(Γ * X)) (β : ℝ) :
    gibbsFunctional H hH β X = 0 := by
  rw [gibbsFunctional_apply]
  have hz := weightedTrace_gibbsDensity_odd_zero H Γ X hH hcomm hΓ hodd β
  rw [weightedTrace_apply] at hz
  rw [hz, mul_zero]

open InfoGeometry.Physics.KleinBottleSewingExact

/-- Real multiples of the existing diagonal Pauli tilt are Hermitian. -/
theorem tiltHamiltonian_isHermitian (h : ℝ) :
    (h • tilt2).IsHermitian := by
  change (h • tilt2).conjTranspose = h • tilt2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, tilt2, RCLike.real_smul_eq_coe_mul]

/-- Diagonal parity and off-diagonal observable, matching the Klein naming
convention. This statement uses the explicit native matrices, not a transported
operator equality from AnomalousKMSFlow. -/
theorem tiltHamiltonian_gibbs_switch_zero (h β : ℝ) :
    gibbsFunctional (h • tilt2) (tiltHamiltonian_isHermitian h) β switch2 = 0 := by
  have hc : Commute (h • tilt2) tilt2 := by
    change (h • tilt2) * tilt2 = tilt2 * (h • tilt2)
    rw [smul_mul_assoc, mul_smul_comm]
  have ho : switch2 * tilt2 = -(tilt2 * switch2) := by
    rw [tilt2_switch2_anticomm, neg_neg]
  exact gibbsFunctional_odd_zero (h • tilt2) tilt2 switch2
    (tiltHamiltonian_isHermitian h) hc tilt2_sq ho β

end
end InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
