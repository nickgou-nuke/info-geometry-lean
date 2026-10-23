/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexificationAlgEquiv
import InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge

/-!
# Prefix cancellation on the corrected binary complex-* quotient

The existing prefix calculus is carried by the tensor-quotient Cuntz algebra.
This owner transports the same algebraic calculation to the corrected
`ComplexStarCuntzAlg Bool` carrier through the proved complexification
equivalence.  It does not use the boundary representation or a scalar word
kernel to infer quotient equality.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge

open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge

abbrev Target := CuntzAlg ℂ Bool
abbrev Source := ComplexStarCuntzAlg Bool

def targetWord : List Bool → Target
  | [] => 1
  | b :: w => S b * targetWord w

def targetWordDag : List Bool → Target
  | [] => 1
  | b :: w => targetWordDag w * T b

theorem targetWord_head_match (b : Bool) (u v : List Bool) :
    targetWordDag (b :: u) * targetWord (b :: v) =
      targetWordDag u * targetWord v := by
  simp only [targetWordDag, targetWord]
  calc
    (targetWordDag u * T b) * (S b * targetWord v) =
        targetWordDag u * (T b * (S b * targetWord v)) := by rw [mul_assoc]
    _ = targetWordDag u * ((T b * S b) * targetWord v) := by
      simp only [mul_assoc]
    _ = targetWordDag u * targetWord v := by
      rw [T_mul_S]
      simp

theorem targetWord_head_mismatch {b c : Bool} (h : b ≠ c)
    (u v : List Bool) :
    targetWordDag (b :: u) * targetWord (c :: v) = 0 := by
  simp only [targetWordDag, targetWord]
  calc
    (targetWordDag u * T b) * (S c * targetWord v) =
        targetWordDag u * (T b * (S c * targetWord v)) := by rw [mul_assoc]
    _ = targetWordDag u * ((T b * S c) * targetWord v) := by
      simp only [mul_assoc]
    _ = 0 := by
      rw [T_mul_S, if_neg h]
      simp

theorem targetWord_prefix_right (u v : List Bool) :
    targetWordDag u * targetWord (u ++ v) = targetWord v := by
  induction u with
  | nil => simp [targetWordDag, targetWord]
  | cons b u ih =>
      rw [List.cons_append, targetWord_head_match]
      exact ih

theorem targetWord_prefix_left (u v : List Bool) :
    targetWordDag (u ++ v) * targetWord u = targetWordDag v := by
  induction u with
  | nil => simp [targetWordDag, targetWord]
  | cons b u ih =>
      rw [List.cons_append, targetWord_head_match]
      exact ih

theorem targetWord_zero_of_prefix_incomparable
    (u v : List Bool)
    (huv : ¬ ∃ t, v = u ++ t)
    (hvu : ¬ ∃ t, u = v ++ t) :
    targetWordDag u * targetWord v = 0 := by
  revert huv hvu
  induction u generalizing v with
  | nil =>
      intro huv hvu
      exact (huv ⟨v, by simp⟩).elim
  | cons b u ih =>
      cases v with
      | nil =>
          intro huv hvu
          exact (hvu ⟨b :: u, by simp⟩).elim
      | cons c v =>
          intro huv hvu
          by_cases hbc : b = c
          · subst c
            have huv' : ¬ ∃ t, v = u ++ t := by
              intro h
              rcases h with ⟨t, ht⟩
              exact huv ⟨t, by simp [ht]⟩
            have hvu' : ¬ ∃ t, u = v ++ t := by
              intro h
              rcases h with ⟨t, ht⟩
              exact hvu ⟨t, by simp [ht]⟩
            rw [targetWord_head_match]
            exact ih v huv' hvu'
          · exact targetWord_head_mismatch hbc u v

theorem targetWord_prefix_cases (u v : List Bool) :
    (∃ t, v = u ++ t ∧
      targetWordDag u * targetWord v = targetWord t) ∨
    (∃ t, u = v ++ t ∧
      targetWordDag u * targetWord v = targetWordDag t) ∨
    ((¬ ∃ t, v = u ++ t) ∧ (¬ ∃ t, u = v ++ t) ∧
      targetWordDag u * targetWord v = 0) := by
  classical
  by_cases huv : ∃ t, v = u ++ t
  · rcases huv with ⟨t, rfl⟩
    exact Or.inl ⟨t, rfl, targetWord_prefix_right u t⟩
  · by_cases hvu : ∃ t, u = v ++ t
    · rcases hvu with ⟨t, rfl⟩
      exact Or.inr (Or.inl ⟨t, rfl, targetWord_prefix_left v t⟩)
    · exact Or.inr (Or.inr ⟨huv, hvu,
        targetWord_zero_of_prefix_incomparable u v huv hvu⟩)

theorem complexStarWord_toLetter (w : List Bool) :
    complexificationAlgEquiv (complexStarWord w) = targetWord w := by
  induction w with
  | nil => simp [complexStarWord, targetWord]
  | cons b w ih =>
      rw [complexStarWord, map_mul, complexificationAlgEquiv_S, ih]
      rfl

theorem complexStarWord_star_toLetter (w : List Bool) :
    complexificationAlgEquiv (star (complexStarWord w)) = targetWordDag w := by
  induction w with
  | nil => simp [complexStarWord, targetWordDag]
  | cons b w ih =>
      rw [complexStarWord, StarMul.star_mul, map_mul, ih,
        star_Sℂ, complexificationAlgEquiv_T]
      rfl

theorem complexStarWord_prefix_right (u v : List Bool) :
    star (complexStarWord u) * complexStarWord (u ++ v) =
      complexStarWord v := by
  apply complexificationAlgEquiv.injective
  rw [map_mul, complexStarWord_star_toLetter, complexStarWord_toLetter,
    complexStarWord_toLetter]
  exact targetWord_prefix_right u v

theorem complexStarWord_prefix_left (u v : List Bool) :
    star (complexStarWord (u ++ v)) * complexStarWord u =
      star (complexStarWord v) := by
  apply complexificationAlgEquiv.injective
  rw [map_mul, complexStarWord_star_toLetter,
    complexStarWord_toLetter, complexStarWord_star_toLetter]
  exact targetWord_prefix_left u v

theorem complexStarWord_zero_of_prefix_incomparable
    (u v : List Bool)
    (huv : ¬ ∃ t, v = u ++ t)
    (hvu : ¬ ∃ t, u = v ++ t) :
    star (complexStarWord u) * complexStarWord v = 0 := by
  apply complexificationAlgEquiv.injective
  rw [map_mul, complexStarWord_star_toLetter, complexStarWord_toLetter,
    map_zero]
  exact targetWord_zero_of_prefix_incomparable u v huv hvu

theorem complexStarWord_prefix_cases (u v : List Bool) :
    (∃ t, v = u ++ t ∧
      star (complexStarWord u) * complexStarWord v = complexStarWord t) ∨
    (∃ t, u = v ++ t ∧
      star (complexStarWord u) * complexStarWord v =
        star (complexStarWord t)) ∨
    ((¬ ∃ t, v = u ++ t) ∧ (¬ ∃ t, u = v ++ t) ∧
      star (complexStarWord u) * complexStarWord v = 0) := by
  classical
  by_cases huv : ∃ t, v = u ++ t
  · rcases huv with ⟨t, rfl⟩
    exact Or.inl ⟨t, rfl, complexStarWord_prefix_right u t⟩
  · by_cases hvu : ∃ t, u = v ++ t
    · rcases hvu with ⟨t, rfl⟩
      exact Or.inr (Or.inl ⟨t, rfl, complexStarWord_prefix_left v t⟩)
    · exact Or.inr (Or.inr ⟨huv, hvu,
        complexStarWord_zero_of_prefix_incomparable u v huv hvu⟩)

end InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge
