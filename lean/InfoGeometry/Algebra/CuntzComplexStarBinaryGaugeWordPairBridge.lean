/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
import InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
import InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore

/-!
# Gauge flow on arbitrary word-pair monomials

This owner extends the corrected binary gauge flow from generators to the full
noncommutative word-pair family.  It is an algebraic covariance theorem; it
does not identify a state with a representation or claim a completed KMS
theorem.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeWordPairBridge

open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
open InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge

abbrev Target := CuntzAlg ℂ Bool
abbrev Source := ComplexStarCuntzAlg Bool

private def phase (z : ℂ) : ℂ := modularPhaseComplex 2 z
private def phaseInv (z : ℂ) : ℂ := modularPhaseComplexInv 2 z

private theorem sigmaBinary_targetWord (z : ℂ) (w : List Bool) :
    sigmaBinary z (targetWord w) = phase z ^ w.length • targetWord w := by
  induction w with
  | nil => simp [targetWord, phase]
  | cons b w ih =>
      rw [targetWord, map_mul, sigmaBinary_S, ih, smul_mul_smul]
      simp only [List.length_cons, pow_succ, phase]
      rw [mul_comm]

private theorem sigmaBinary_targetWordDag (z : ℂ) (w : List Bool) :
    sigmaBinary z (targetWordDag w) = phaseInv z ^ w.length • targetWordDag w := by
  induction w with
  | nil => simp [targetWordDag, phaseInv]
  | cons b w ih =>
      rw [targetWordDag, map_mul, ih, sigmaBinary_T, smul_mul_smul]
      simp only [List.length_cons, pow_succ, phaseInv]

theorem sigmaBinary_targetWordPair (z : ℂ) (u v : List Bool) :
    sigmaBinary z (targetWord u * targetWordDag v) =
      (phase z ^ u.length * phaseInv z ^ v.length) •
        (targetWord u * targetWordDag v) := by
  rw [map_mul, sigmaBinary_targetWord, sigmaBinary_targetWordDag,
    smul_mul_smul]

theorem carrierFlow_wordPair (z : ℂ) (u v : List Bool) :
    carrierFlow z (complexStarWordPair u v) =
      (phase z ^ u.length * phaseInv z ^ v.length) •
        complexStarWordPair u v := by
  unfold complexStarWordPair
  rw [map_mul, carrierFlow_word, carrierFlow_star_word, smul_mul_smul]
  simp [phase, phaseInv]

end InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeWordPairBridge
