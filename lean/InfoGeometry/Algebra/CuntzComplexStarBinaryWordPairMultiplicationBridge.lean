/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge

/-!
# Multiplication of arbitrary word-pair monomials on the corrected quotient

The reduction owner supplies the genuine prefix trichotomy for the middle
factor.  This owner lifts it to products of arbitrary word-pair monomials on
the same quotient carrier.  No finite matrix restriction, boundary-state
readout, or scalar word-span multiplication is introduced.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge

theorem complexStarWord_append (u v : List Bool) :
    complexStarWord (u ++ v) = complexStarWord u * complexStarWord v := by
  induction u with
  | nil => simp [complexStarWord]
  | cons b u ih =>
      simp only [List.cons_append, complexStarWord]
      rw [ih, mul_assoc]

theorem complexStarWord_star_append (u v : List Bool) :
    star (complexStarWord (u ++ v)) =
      star (complexStarWord v) * star (complexStarWord u) := by
  rw [complexStarWord_append, StarMul.star_mul]

def complexStarWordPair (u v : List Bool) : ComplexStarCuntzAlg Bool :=
  complexStarWord u * star (complexStarWord v)

theorem complexStarWordPair_mul_prefix_cases (u v x y : List Bool) :
    (∃ t, x = v ++ t ∧
      complexStarWordPair u v * complexStarWordPair x y =
        complexStarWordPair (u ++ t) y) ∨
    (∃ t, v = x ++ t ∧
      complexStarWordPair u v * complexStarWordPair x y =
        complexStarWordPair u (y ++ t)) ∨
    ((¬ ∃ t, x = v ++ t) ∧ (¬ ∃ t, v = x ++ t) ∧
      complexStarWordPair u v * complexStarWordPair x y = 0) := by
  rcases complexStarWord_prefix_cases v x with h | h | h
  · rcases h with ⟨t, rfl, hred⟩
    left
    refine ⟨t, rfl, ?_⟩
    unfold complexStarWordPair
    calc
      (complexStarWord u * star (complexStarWord v)) *
          (complexStarWord (v ++ t) * star (complexStarWord y)) =
          complexStarWord u *
            (star (complexStarWord v) * complexStarWord (v ++ t)) *
            star (complexStarWord y) := by simp [mul_assoc]
      _ = complexStarWord u * complexStarWord t *
            star (complexStarWord y) := by rw [hred]
      _ = complexStarWordPair (u ++ t) y := by
        simp only [complexStarWordPair]
        rw [complexStarWord_append]
  · rcases h with ⟨t, rfl, hred⟩
    right
    left
    refine ⟨t, rfl, ?_⟩
    unfold complexStarWordPair
    calc
      (complexStarWord u * star (complexStarWord (x ++ t))) *
          (complexStarWord x * star (complexStarWord y)) =
          complexStarWord u *
            (star (complexStarWord (x ++ t)) * complexStarWord x) *
            star (complexStarWord y) := by simp [mul_assoc]
      _ = complexStarWord u * star (complexStarWord t) *
            star (complexStarWord y) := by rw [hred]
      _ = complexStarWordPair u (y ++ t) := by
        simp only [complexStarWordPair]
        rw [complexStarWord_star_append]
        simp only [mul_assoc]
  · rcases h with ⟨huv, hvu, hzero⟩
    right
    right
    refine ⟨huv, hvu, ?_⟩
    unfold complexStarWordPair
    calc
      (complexStarWord u * star (complexStarWord v)) *
          (complexStarWord x * star (complexStarWord y)) =
          complexStarWord u *
            (star (complexStarWord v) * complexStarWord x) *
            star (complexStarWord y) := by simp [mul_assoc]
      _ = 0 := by simp [hzero]

end InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
