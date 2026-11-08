import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeCutoffNative

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeCutoffFiniteEuler

open InfoGeometry.Arithmetic.PrimeCutoffNative

theorem boson_mul_signed_cancel
    {R : Type*} [Field R] (M : ℕ)
    (x : PrimeCutoff M → R)
    (h : ∀ p, 1 - x p ≠ 0) :
    (∏ p : PrimeCutoff M, (1 - x p)⁻¹) *
        ∏ p : PrimeCutoff M, (1 - x p) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_eq_one
  intro p
  exact inv_mul_cancel₀ (h p)

theorem signed_cancel_boson
    {R : Type*} [Field R] (M : ℕ)
    (x : PrimeCutoff M → R)
    (h : ∀ p, 1 - x p ≠ 0) :
    (∏ p : PrimeCutoff M, (1 - x p)) *
        ∏ p : PrimeCutoff M, (1 - x p)⁻¹ = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_eq_one
  intro p
  exact mul_inv_cancel₀ (h p)

theorem boson_mul_square_signed_eq_positive
    {R : Type*} [Field R] (M : ℕ)
    (x : PrimeCutoff M → R)
    (h : ∀ p, 1 - x p ≠ 0) :
    (∏ p : PrimeCutoff M, (1 - x p)⁻¹) *
        ∏ p : PrimeCutoff M, (1 - x p * x p) =
      ∏ p : PrimeCutoff M, (1 + x p) := by
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro p
  calc
    (1 - x p)⁻¹ * (1 - x p * x p) =
        (1 - x p)⁻¹ * ((1 - x p) * (1 + x p)) := by ring
    _ = ((1 - x p)⁻¹ * (1 - x p)) * (1 + x p) := by ring
    _ = 1 * (1 + x p) := by rw [inv_mul_cancel₀ (h p)]
    _ = 1 + x p := by ring

end InfoGeometry.Arithmetic.PrimeCutoffFiniteEuler
