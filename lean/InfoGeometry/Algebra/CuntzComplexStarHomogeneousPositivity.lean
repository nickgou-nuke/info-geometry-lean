/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents

/-! Homogeneous star-squares reduce to finite sums of squares in the core. -/
noncomputable section
namespace InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents

open scoped ComplexOrder
open InfoGeometry.Algebra.CuntzIntegerGrading
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreMatrixUnits
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

theorem mem_core_of_degree_zero {a : Carrier}
    (ha : delta a = AddMonoidAlgebra.single 0 a) : a ∈ core := by
  have he : projection a = a := by
    change (delta a).coeff 0 = a
    rw [ha]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  rw [← he]
  exact projection_mem_core a

theorem homogeneous_nat_square_nonneg (f : Carrier →ₗ[ℂ] ℂ)
    (hf : ∀ b ∈ core, 0 ≤ f (star b * b)) (n : ℕ) (a : Carrier)
    (ha : delta a = AddMonoidAlgebra.single (n : ℤ) a) :
    0 ≤ f (star a * a) := by
  have hc (w : BitWord n) : star (complexStarWord (List.ofFn w)) * a ∈ core := by
    apply mem_core_of_degree_zero
    rw [map_mul, delta_star_word, ha, AddMonoidAlgebra.single_mul_single]
    simp only [List.length_ofFn, neg_add_cancel]
  have hs : star a * a = ∑ w : BitWord n,
      star (star (complexStarWord (List.ofFn w)) * a) *
        (star (complexStarWord (List.ofFn w)) * a) := by
    calc star a * a = star a *
        (∑ w : BitWord n, complexStarWordPair (List.ofFn w) (List.ofFn w)) * a := by
          rw [wordPair_level_sum, mul_one]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        simp only [complexStarWordPair, star_mul, star_star, mul_assoc]
  rw [hs, map_sum]
  exact Finset.sum_nonneg (fun w _ => hf _ (hc w))

theorem homogeneous_neg_nat_square_nonneg (f : Carrier →ₗ[ℂ] ℂ)
    (hf : ∀ b ∈ core, 0 ≤ f (star b * b)) (n : ℕ) (a : Carrier)
    (ha : delta a = AddMonoidAlgebra.single (-(n : ℤ)) a) :
    0 ≤ f (star a * a) := by
  let w := List.replicate n false
  have hc : complexStarWord w * a ∈ core := by
    apply mem_core_of_degree_zero
    rw [map_mul, delta_word, ha, AddMonoidAlgebra.single_mul_single]
    simp only [w, List.length_replicate, add_neg_cancel]
  have hw : star (complexStarWord w) * complexStarWord w = 1 := by
    simpa using word_cancel_equal_length w w rfl
  have hs : star (complexStarWord w * a) * (complexStarWord w * a) = star a * a := by
    rw [star_mul]
    calc star a * star (complexStarWord w) * (complexStarWord w * a)
      _ = star a * (star (complexStarWord w) * complexStarWord w) * a := by
        simp only [mul_assoc]
      _ = star a * a := by rw [hw, mul_one]
  simpa only [hs] using hf _ hc

theorem homogeneous_square_nonneg (f : Carrier →ₗ[ℂ] ℂ)
    (hf : ∀ b ∈ core, 0 ≤ f (star b * b)) (d : ℤ) (a : Carrier)
    (ha : delta a = AddMonoidAlgebra.single d a) : 0 ≤ f (star a * a) := by
  cases d with
  | ofNat n => exact homogeneous_nat_square_nonneg f hf n a ha
  | negSucc n =>
      apply homogeneous_neg_nat_square_nonneg f hf (n + 1) a
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      rw [hn] at ha
      exact ha

end InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents
end
