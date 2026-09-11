import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Hestenes Paravector and Chiral Sheet-Flipping Bridge

This module formalizes the structural equivalence between:
1. Hodge duality on odd multivectors and the Hestenes Hermitian adjoint on even paravectors.
2. Odd Clifford multiplication and the chiral sheet-flipping operation.
-/

variable {A : Type*} [Ring A]
variable (γ₀ : A) (Ω₄ : A) (Γ₅ : A) (P_plus P_minus : A)
variable (rev : A → A)

/-- The Hestenes Hermitian adjoint on the even paravector algebra. -/
def hestenesAdjoint (a : A) : A :=
  γ₀ * rev a * γ₀

/-- The right odd-even conversion map ρ_R(x) = x γ₀. -/
def rhoR (x : A) : A :=
  x * γ₀

/-- Hodge duality defined via reversion and the pseudoscalar. -/
def hodgeStar (x : A) : A :=
  rev x * Ω₄

/-- The structural bridge connecting Hodge duality to the Hestenes paravector algebra.
If `γ₀` squares to 1, and `Ω₄` anti-commutes with `γ₀`, then
`ρ_R(⋆ x) = - ρ_R(x)^{†_H} Ω₄` follows algebraically. -/
theorem rhoR_hodgeStar (x : A)
    (h_rev_mul : ∀ a b, rev (a * b) = rev b * rev a)
    (h_rev_gamma0 : rev γ₀ = γ₀)
    (h_gamma0_sq : γ₀ * γ₀ = 1)
    (h_omega4_anticomm : Ω₄ * γ₀ = -γ₀ * Ω₄) :
    rhoR γ₀ (hodgeStar Ω₄ rev x) = - (hestenesAdjoint γ₀ rev (rhoR γ₀ x) * Ω₄) := by
  -- ρ_R(⋆ x) = (rev x * Ω₄) * γ₀
  -- = rev x * (Ω₄ * γ₀)
  -- = rev x * (-γ₀ * Ω₄)
  -- = - (rev x * γ₀) * Ω₄
  
  -- RHS: - (γ₀ * rev(x * γ₀) * γ₀) * Ω₄
  -- = - (γ₀ * (rev γ₀ * rev x) * γ₀) * Ω₄
  -- = - (γ₀ * (γ₀ * rev x) * γ₀) * Ω₄
  -- = - (γ₀^2 * rev x * γ₀) * Ω₄
  -- = - (rev x * γ₀) * Ω₄
  
  calc
    rhoR γ₀ (hodgeStar Ω₄ rev x)
      = (rev x * Ω₄) * γ₀ := rfl
    _ = rev x * (Ω₄ * γ₀) := by rw [mul_assoc]
    _ = rev x * (-γ₀ * Ω₄) := by rw [h_omega4_anticomm]
    _ = - (rev x * γ₀ * Ω₄) := by rw [neg_mul, mul_neg, ← mul_assoc]
    _ = - (1 * rev x * γ₀ * Ω₄) := by simp
    _ = - ((γ₀ * γ₀) * rev x * γ₀ * Ω₄) := by rw [h_gamma0_sq]
    _ = - (γ₀ * (γ₀ * rev x) * γ₀ * Ω₄) := by simp [mul_assoc]
    _ = - (γ₀ * (rev γ₀ * rev x) * γ₀ * Ω₄) := by rw [h_rev_gamma0]
    _ = - (γ₀ * rev (x * γ₀) * γ₀ * Ω₄) := by rw [h_rev_mul]
    _ = - (hestenesAdjoint γ₀ rev (rhoR γ₀ x) * Ω₄) := rfl

/-- Odd Clifford multiplication acts as the exact chiral sheet-flipping operation.
If a vector `v` anti-commutes with `Γ₅`, then `v` intertwines the Weyl projectors. -/
theorem chiral_sheet_flip (v : A)
    (h_Γ₅_anticomm : Γ₅ * v = - (v * Γ₅))
    (h_P_plus : P_plus = (1 + Γ₅))
    (h_P_minus : P_minus = (1 - Γ₅)) :
    P_plus * v = v * P_minus ∧ P_minus * v = v * P_plus := by
  constructor
  · calc
      P_plus * v = (1 + Γ₅) * v := by rw [h_P_plus]
      _ = v + Γ₅ * v := by rw [add_mul, one_mul]
      _ = v - v * Γ₅ := by rw [h_Γ₅_anticomm, sub_eq_add_neg]
      _ = v * (1 - Γ₅) := by rw [mul_sub, mul_one]
      _ = v * P_minus := by rw [h_P_minus]
  · calc
      P_minus * v = (1 - Γ₅) * v := by rw [h_P_minus]
      _ = v - Γ₅ * v := by rw [sub_mul, one_mul]
      _ = v - -(v * Γ₅) := by rw [h_Γ₅_anticomm]
      _ = v + v * Γ₅ := by rw [sub_neg_eq_add]
      _ = v * (1 + Γ₅) := by rw [mul_add, mul_one]
      _ = v * P_plus := by rw [h_P_plus]

end InfoGeometry.Canonical
