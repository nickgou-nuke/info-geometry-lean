/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzIntegerGradingEmbedding
import InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge

/-!
# Degree-zero extraction on the corrected binary Cuntz quotient

The integer grading is an algebra map from the full corrected quotient into an
additive monoid algebra whose coefficients are still the noncommutative
quotient.  This owner extracts the coefficient at degree zero and computes it
on arbitrary word-pair monomials.  It is a linear readout, not an algebra
homomorphism, and it asserts neither positivity nor state normalization.
In particular, no diagonalizability or commutativity hypothesis is used.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzIntegerGrading
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge

abbrev Carrier := ComplexStarCuntzAlg Bool
abbrev Graded := AddMonoidAlgebra Carrier ℤ

def degreeZero : Graded →ₗ[ℂ] Carrier where
  toFun p := p.coeff 0
  map_add' p q := by simp
  map_smul' c p := by simp

theorem delta_word (w : List Bool) :
    delta (complexStarWord w) =
      AddMonoidAlgebra.single (w.length : ℤ) (complexStarWord w) := by
  induction w with
  | nil => simp [complexStarWord, delta]
  | cons b w ih =>
      simp only [complexStarWord, map_mul, delta_S, ih,
        AddMonoidAlgebra.single_mul_single]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [add_comm]

theorem delta_star_word (w : List Bool) :
    delta (star (complexStarWord w)) =
      AddMonoidAlgebra.single (-(w.length : ℤ)) (star (complexStarWord w)) := by
  induction w with
  | nil => simp [complexStarWord, delta]
  | cons b w ih =>
      simp only [complexStarWord, StarMul.star_mul, map_mul, ih,
        star_Sℂ, delta_T, AddMonoidAlgebra.single_mul_single]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [neg_add]

theorem delta_wordPair (u v : List Bool) :
    delta (complexStarWordPair u v) =
      AddMonoidAlgebra.single ((u.length : ℤ) - (v.length : ℤ))
        (complexStarWordPair u v) := by
  unfold complexStarWordPair
  rw [map_mul, delta_word, delta_star_word,
    AddMonoidAlgebra.single_mul_single]
  simp only [sub_eq_add_neg]

theorem degreeZero_delta_wordPair (u v : List Bool) :
    degreeZero (delta (complexStarWordPair u v)) =
      if u.length = v.length then complexStarWordPair u v else 0 := by
  rw [delta_wordPair]
  change (AddMonoidAlgebra.single ((u.length : ℤ) - (v.length : ℤ))
      (complexStarWordPair u v)).coeff 0 = _
  by_cases h : u.length = v.length
  · have hz : (u.length : ℤ) - (v.length : ℤ) = 0 := by omega
    rw [hz]
    change (Finsupp.single (0 : ℤ) (complexStarWordPair u v)) 0 = _
    simp [h]
  · have hne : (u.length : ℤ) - (v.length : ℤ) ≠ 0 := by omega
    change (Finsupp.single ((u.length : ℤ) - (v.length : ℤ))
      (complexStarWordPair u v)) 0 = _
    simp [hne, h]

theorem degreeZero_delta_finiteStageElement
    (n : ℕ) (A : BitWordMatrixStage n) :
    degreeZero (delta (complexStarFiniteStageElement n A)) =
      complexStarFiniteStageElement n A := by
  unfold complexStarFiniteStageElement
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change A u v • degreeZero
      (delta (complexStarWordPair (List.ofFn u) (List.ofFn v))) =
    A u v • complexStarWordPair (List.ofFn u) (List.ofFn v)
  rw [degreeZero_delta_wordPair]
  simp

end InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
