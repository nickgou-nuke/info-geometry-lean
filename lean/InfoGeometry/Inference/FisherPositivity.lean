/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.TCSSensitivity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Fisher-information positivity

The finite Fisher matrix is positive semidefinite because its quadratic form is
a weighted sum of squares. This theorem does not assume invertibility; an
inverse-Hessian covariance interpretation requires a separate nonsingularity
contract.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

theorem fisherInformation_quadratic_nonneg
    (w : Data → ℝ) (sensitivity : Data → Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (v : Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * fisherInformation w sensitivity a b * v b := by
  simp only [fisherInformation]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hreorder :
      (∑ x : Fin 2, ∑ y : Fin 2, ∑ i : Data,
        v x * (w i * sensitivity i x * sensitivity i y) * v y) =
        ∑ i : Data, ∑ x : Fin 2, ∑ y : Fin 2,
          v x * (w i * sensitivity i x * sensitivity i y) * v y := by
    calc
      _ = ∑ x : Fin 2, ∑ i : Data, ∑ y : Fin 2,
          v x * (w i * sensitivity i x * sensitivity i y) * v y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hreorder]
  apply Finset.sum_nonneg
  intro i hi
  have hfactor :
      (∑ x : Fin 2, ∑ y : Fin 2,
        v x * (w i * sensitivity i x * sensitivity i y) * v y) =
        w i * (∑ x : Fin 2, v x * sensitivity i x) ^ 2 := by
    calc
      _ = (∑ x : Fin 2, v x * sensitivity i x) *
          (∑ y : Fin 2, sensitivity i y * v y) * w i := by
        rw [Fintype.sum_mul_sum]
        simp only [mul_assoc, mul_comm, mul_left_comm]
        simp_rw [Finset.mul_sum]
      _ = w i * (∑ x : Fin 2, v x * sensitivity i x) ^ 2 := by
        have hsum :
            (∑ y : Fin 2, sensitivity i y * v y) =
              ∑ x : Fin 2, v x * sensitivity i x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        rw [hsum]
        ring
  rw [hfactor]
  exact mul_nonneg (hw i) (sq_nonneg _)

end InfoGeometry.Inference
