/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
import InfoGeometry.Algebra.CuntzQuotientDiracBridge
import InfoGeometry.Canonical.CuntzWordReduction
import InfoGeometry.Canonical.MatrixAlgebraCuntzEmbedding

/-!
# Quotient-level Cuntz word reduction

Transport the generic Cuntz word calculus to the repository's tensor-algebra
quotient using its existing `quotientCuntzNAlgebra` realization.  This keeps
the quotient's native word owners and the reusable abstract reduction aligned.
-/

namespace InfoGeometry.Canonical.CuntzQuotientWordReductionBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

theorem quotientCuntzWord_eq_generic
    (n : ℕ) (w : List (Fin n)) :
    CuntzAlgebra.wordS
        (InfoGeometry.Algebra.CuntzQuotientDiracBridge.quotientCuntzNAlgebra n) w =
      cuntzWordShift w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change cuntzS n i *
          CuntzAlgebra.wordS
            (InfoGeometry.Algebra.CuntzQuotientDiracBridge.quotientCuntzNAlgebra n) w =
        cuntzS n i * cuntzWordShift w
      rw [ih]

theorem quotientCuntzWordStar_eq_generic
    (n : ℕ) (w : List (Fin n)) :
    CuntzAlgebra.wordSStar
        (InfoGeometry.Algebra.CuntzQuotientDiracBridge.quotientCuntzNAlgebra n) w =
      cuntzWordShiftDag w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change CuntzAlgebra.wordSStar
            (InfoGeometry.Algebra.CuntzQuotientDiracBridge.quotientCuntzNAlgebra n) w *
          star (cuntzS n i) =
        cuntzWordShiftDag w * cuntzSdag n i
      rw [star_cuntzS, ih]

/-- Full prefix cancellation on the actual tensor-quotient Cuntz words. -/
theorem cuntzWordShift_prefix_cases
    {n : ℕ} (v x : List (Fin n)) :
    (∃ t, x = v ++ t ∧
      cuntzWordShiftDag v * cuntzWordShift x = cuntzWordShift t) ∨
    (∃ t, v = x ++ t ∧
      cuntzWordShiftDag v * cuntzWordShift x = cuntzWordShiftDag t) ∨
    ((¬ ∃ t, x = v ++ t) ∧ (¬ ∃ t, v = x ++ t) ∧
      cuntzWordShiftDag v * cuntzWordShift x = 0) := by
  simpa only [quotientCuntzWord_eq_generic,
    quotientCuntzWordStar_eq_generic] using
      CuntzAlgebra.word_reduction_prefix_cases
        (InfoGeometry.Algebra.CuntzQuotientDiracBridge.quotientCuntzNAlgebra n)
        v x

/-- Products of quotient Cuntz monomials reduce by prefix cancellation at
arbitrary word lengths. -/
theorem cuntzWordMonomial_mul_prefix_cases
    {n : ℕ} (α β γ δ : List (Fin n)) :
    (∃ t, γ = β ++ t ∧
      (cuntzWordShift α * cuntzWordShiftDag β) *
          (cuntzWordShift γ * cuntzWordShiftDag δ) =
        cuntzWordShift (α ++ t) * cuntzWordShiftDag δ) ∨
    (∃ t, β = γ ++ t ∧
      (cuntzWordShift α * cuntzWordShiftDag β) *
          (cuntzWordShift γ * cuntzWordShiftDag δ) =
        cuntzWordShift α * cuntzWordShiftDag (δ ++ t)) ∨
    ((¬ ∃ t, γ = β ++ t) ∧ (¬ ∃ t, β = γ ++ t) ∧
      (cuntzWordShift α * cuntzWordShiftDag β) *
          (cuntzWordShift γ * cuntzWordShiftDag δ) = 0) := by
  simpa only [CuntzAlgebra.matrixUnit, quotientCuntzWord_eq_generic,
    quotientCuntzWordStar_eq_generic] using
      CuntzAlgebra.matrixUnit_mul_prefix_cases
        (InfoGeometry.Algebra.CuntzQuotientDiracBridge.quotientCuntzNAlgebra n)
        α β γ δ

end InfoGeometry.Canonical.CuntzQuotientWordReductionBridge
