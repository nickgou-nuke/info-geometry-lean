import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CantorKMSState

/-!
# Holographic Boundary Entropy and the Area Law

This module formalizes the von Neumann entropy of boundary diagonal states and proves the
holographic Area Law: the entropy of the maximally mixed state at stage `n` is strictly
linear in the boundary horizon area `n` (prefix depth).
-/

noncomputable section

namespace InfoGeometry.Canonical.HolographicBoundaryEntropy

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState

/-- Condition for a state to be a valid density matrix at stage n. -/
def IsDensityMatrix (n : ℕ) (ρ : DiagAlg n) : Prop :=
  (∀ w, 0 ≤ (ρ w).re) ∧ (Finset.sum Finset.univ (fun w => (ρ w).re) = 1)

/-- The von Neumann entropy of a state at stage n. -/
def vonNeumannEntropy (n : ℕ) (ρ : DiagAlg n) : ℝ :=
  - Finset.sum Finset.univ (fun w => (ρ w).re * Real.log (ρ w).re)

/-- The maximally mixed state at stage n. -/
def maximallyMixedState (n : ℕ) : DiagAlg n :=
  fun _ => (2 : ℂ)⁻¹ ^ n

theorem maximallyMixedState_re (n : ℕ) (w : BitWord n) :
    (maximallyMixedState n w).re = (2 : ℝ)⁻¹ ^ n := by
  dsimp [maximallyMixedState]
  have h_eq : ((2 : ℂ)⁻¹ ^ n) = (↑((2 : ℝ)⁻¹ ^ n) : ℂ) := by
    push_cast
    rfl
  rw [h_eq]
  exact Complex.ofReal_re ((2 : ℝ)⁻¹ ^ n)

theorem maximallyMixedState_is_density (n : ℕ) :
    IsDensityMatrix n (maximallyMixedState n) := by
  constructor
  · intro w
    rw [maximallyMixedState_re]
    positivity
  · have h_sum : Finset.sum Finset.univ (fun w : BitWord n => (maximallyMixedState n w).re) =
        Finset.sum Finset.univ (fun _ : BitWord n => (2 : ℝ)⁻¹ ^ n) := by
      congr 1
      ext w
      exact maximallyMixedState_re n w
    rw [h_sum]
    have h_card : Finset.sum Finset.univ (fun _ : BitWord n => (2 : ℝ)⁻¹ ^ n) =
        Fintype.card (BitWord n) * (2 : ℝ)⁻¹ ^ n := by
      simp
    rw [h_card, card_BitWord, Nat.cast_pow, Nat.cast_two]
    have h_pow : (2 : ℝ)⁻¹ ^ n = (2^n : ℝ)⁻¹ := by
      rw [inv_pow]
    rw [h_pow]
    have h_nonzero : (2^n : ℝ) ≠ 0 := by
      exact pow_ne_zero n (by norm_num)
    exact mul_inv_cancel₀ h_nonzero

/-- The Holographic Area Law: the von Neumann entropy of the boundary
vacuum state is strictly linear in the prefix depth (area) `n`. -/
theorem holographic_area_law (n : ℕ) :
    vonNeumannEntropy n (maximallyMixedState n) = (n : ℝ) * Real.log 2 := by
  dsimp [vonNeumannEntropy]
  have h_term : (fun w : BitWord n => (maximallyMixedState n w).re * Real.log (maximallyMixedState n w).re) =
      (fun _ => (2 : ℝ)⁻¹ ^ n * Real.log ((2 : ℝ)⁻¹ ^ n)) := by
    ext w
    rw [maximallyMixedState_re]
  rw [h_term]
  have h_sum : Finset.sum Finset.univ (fun _ : BitWord n => (2 : ℝ)⁻¹ ^ n * Real.log ((2 : ℝ)⁻¹ ^ n)) =
      Fintype.card (BitWord n) * ((2 : ℝ)⁻¹ ^ n * Real.log ((2 : ℝ)⁻¹ ^ n)) := by
    simp
  rw [h_sum, card_BitWord, Nat.cast_pow, Nat.cast_two]
  have h_pow : (2 : ℝ)⁻¹ ^ n = (2^n : ℝ)⁻¹ := by
    rw [inv_pow]
  rw [h_pow]
  rw [← mul_assoc]
  have h_nonzero : (2^n : ℝ) ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  rw [mul_inv_cancel₀ h_nonzero, one_mul]
  have h_log_inv : Real.log (2^n : ℝ)⁻¹ = - Real.log (2^n : ℝ) := by
    exact Real.log_inv (2^n : ℝ)
  rw [h_log_inv]
  simp only [neg_neg]
  exact Real.log_pow 2 n

end InfoGeometry.Canonical.HolographicBoundaryEntropy

end noncomputable section
