/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge

/-!
# Binary gauge invariance of the full finite noncommutative core

The binary flow acts on arbitrary creation/annihilation word pairs.  Equal
depth pairs have opposite degree, so every matrix unit in an equal-depth UHF
stage is fixed.  The final theorem therefore covers arbitrary matrices, not
only diagonal matrices or diagonalizable operators.

This is finite algebraic core invariance.  It does not assert a positive KMS
functional on an infinite completion or an analytic modular theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeFlow
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

abbrev Carrier := ComplexStarCuntzAlg Bool

theorem carrierFlow_word (z : ℂ) (w : List Bool) :
    carrierFlow z (complexStarWord w) =
      modularPhaseComplex 2 z ^ w.length • complexStarWord w := by
  induction w with
  | nil => simp [complexStarWord]
  | cons b w ih =>
      rw [complexStarWord, map_mul, carrierFlow_S, ih, smul_mul_smul]
      simp only [List.length_cons, Nat.succ_eq_add_one]
      rw [pow_succ]

      simp [mul_comm, mul_left_comm, mul_assoc]

theorem carrierFlow_star_word (z : ℂ) (w : List Bool) :
    carrierFlow z (star (complexStarWord w)) =
      modularPhaseComplexInv 2 z ^ w.length • star (complexStarWord w) := by
  induction w with
  | nil => simp [complexStarWord]
  | cons b w ih =>
      rw [complexStarWord, star_mul, map_mul, ih, star_Sℂ, carrierFlow_T,
        smul_mul_smul]
      simp only [List.length_cons, Nat.succ_eq_add_one]
      rw [pow_succ]

theorem carrierFlow_matrixUnit (z : ℂ) (n : ℕ)
    (u v : BitWord n) :
    carrierFlow z
        (complexStarWord (List.ofFn u) *
          star (complexStarWord (List.ofFn v))) =
      complexStarWord (List.ofFn u) *
        star (complexStarWord (List.ofFn v)) := by
  rw [map_mul, carrierFlow_word, carrierFlow_star_word]
  rw [List.length_ofFn, List.length_ofFn, smul_mul_smul]
  have hphase :
      modularPhaseComplex 2 z ^ n * modularPhaseComplexInv 2 z ^ n = 1 := by
    rw [← mul_pow, modularPhaseComplex_mul_inv, one_pow]
  rw [hphase, one_smul]

theorem carrierFlow_finiteStageElement (z : ℂ) (n : ℕ)
    (A : BitWordMatrixStage n) :
    carrierFlow z (complexStarFiniteStageElement n A) =
      complexStarFiniteStageElement n A := by
  unfold complexStarFiniteStageElement
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_smul, carrierFlow_matrixUnit]

/-! The restriction of the full carrier flow to an equal-depth matrix core is
the identity.  The realization theorem below makes this restriction explicit;
it is not an independently introduced diagonal dynamics. -/

def finiteCoreFlow (n : ℕ) (z : ℂ) :
    BitWordMatrixStage n →ₐ[ℂ] BitWordMatrixStage n :=
  AlgHom.id ℂ (BitWordMatrixStage n)

theorem finiteCoreFlow_realizes_carrierFlow (z : ℂ) (n : ℕ)
    (A : BitWordMatrixStage n) :
    complexStarFiniteStageElement n (finiteCoreFlow n z A) =
      carrierFlow z (complexStarFiniteStageElement n A) := by
  simpa [finiteCoreFlow] using
    (carrierFlow_finiteStageElement z n A).symm

def finiteCoreState (n : ℕ) : BitWordMatrixStage n →ₗ[ℂ] ℂ :=
  bitWordMatrixTraceFunctional n

/-! This is the finite equal-depth KMS boundary identity for arbitrary matrix
elements.  The dynamics is the proved restriction of the full binary carrier
flow, and the state is the normalized noncommutative matrix trace. -/

theorem finiteCore_kms_boundary (z : ℂ) (n : ℕ)
    (A B : BitWordMatrixStage n) :
    finiteCoreState n (A * finiteCoreFlow n z B) =
      finiteCoreState n (B * A) := by
  simp only [finiteCoreState, finiteCoreFlow, AlgHom.id_apply]
  rw [← bitWordMatrixGaugeReadout_eq_trace n (A * B),
    ← bitWordMatrixGaugeReadout_eq_trace n (B * A)]
  exact bitWordMatrixGaugeReadout_mul_comm n A B

end InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
