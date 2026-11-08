/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge

/-! Matrix-unit multiplication and right-extension refinement inside the
corrected quotient itself. No faithfulness of a boundary representation is
assumed to obtain these equalities.
-/
noncomputable section
namespace InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState

/-- Inserting the Cuntz partition extends both words on the right. -/
theorem wordPair_refinement (u v : List Bool) :
    (∑ b : Bool, complexStarWordPair (u ++ [b]) (v ++ [b])) =
      complexStarWordPair u v := by
  simp only [complexStarWordPair, complexStarWord_append, complexStarWord,
    mul_one, star_mul, star_Sℂ]
  calc
    (∑ b : Bool, (complexStarWord u * Sℂ b) * (Tℂ b * star (complexStarWord v))) =
        complexStarWord u * (∑ b : Bool, Sℂ b * Tℂ b) * star (complexStarWord v) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = complexStarWord u * star (complexStarWord v) := by
      rw [complexified_partition, mul_one]

/-- Equal-length cancellation holds in the quotient, before representation. -/
theorem word_cancel_equal_length (u v : List Bool) (h : u.length = v.length) :
    star (complexStarWord u) * complexStarWord v = if u = v then 1 else 0 := by
  rcases complexStarWord_prefix_cases u v with hright | hleft | hzero
  · obtain ⟨t, rfl, ht⟩ := hright
    have ht0 : t = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_append] at h
      omega
    subst t
    simpa [complexStarWord] using ht
  · obtain ⟨t, rfl, ht⟩ := hleft
    have ht0 : t = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_append] at h
      omega
    subst t
    simpa [complexStarWord] using ht
  · obtain ⟨hne, _, hz⟩ := hzero
    have huv : u ≠ v := by
      intro heq
      apply hne
      exact ⟨[], by simp [heq]⟩
    simp [huv, hz]

/-- Multiplication contracts the middle equal-depth indices. -/
theorem wordPair_mul_equal_length (u v x y : List Bool) (h : v.length = x.length) :
    complexStarWordPair u v * complexStarWordPair x y =
      if v = x then complexStarWordPair u y else 0 := by
  unfold complexStarWordPair
  calc
    (complexStarWord u * star (complexStarWord v)) *
        (complexStarWord x * star (complexStarWord y)) =
      complexStarWord u * (star (complexStarWord v) * complexStarWord x) *
        star (complexStarWord y) := by simp only [mul_assoc]
    _ = _ := by rw [word_cancel_equal_length v x h]; split_ifs <;> simp

theorem wordPair_star (u v : List Bool) :
    star (complexStarWordPair u v) = complexStarWordPair v u := by
  simp [complexStarWordPair, star_mul]

/-- At every finite depth the diagonal word units resolve the quotient unit. -/
theorem wordPair_level_sum (n : ℕ) :
    (∑ w : BitWord n, complexStarWordPair (List.ofFn w) (List.ofFn w)) = 1 := by
  induction n with
  | zero => simp [complexStarWordPair, complexStarWord]
  | succ n ih =>
      rw [← (bitWordEquiv n).symm.sum_comp
        (fun w => complexStarWordPair (List.ofFn w) (List.ofFn w))]
      rw [← Finset.univ_product_univ, Finset.sum_product]
      have h : ∀ w : BitWord n,
          (∑ b : Bool, complexStarWordPair
            (List.ofFn ((bitWordEquiv n).symm (w, b)))
            (List.ofFn ((bitWordEquiv n).symm (w, b)))) =
          complexStarWordPair (List.ofFn w) (List.ofFn w) := by
        intro w
        change (∑ b : Bool, complexStarWordPair
          (List.ofFn (extendBitWord n w b)) (List.ofFn (extendBitWord n w b))) = _
        simp_rw [list_ofFn_extendBitWord]
        exact wordPair_refinement _ _
      simpa only [h] using ih

end InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits
end
