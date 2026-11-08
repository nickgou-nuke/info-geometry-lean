/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.GeneratorDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset

/-!
# Idempotency defect in the Peirce charge channels

The metric defect is retained as an operator. This module records its exact
Peirce-channel form and the already-proved double-commutator mismatches. The
five-grade Zorn endomorphism carrier is a separate structure and is not
identified with these Peirce charges here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/- The defect remains neutral for the Peirce grading, so multiplying either
directed cone by it preserves that cone's extreme charge. -/
theorem idempotency_defect_weighted_cones_keep_extreme_charges
    {P : B} (hP : P * P = P) (A C : B) :
    let δ := idempotencyDefect (genV P A C)
    comm (invS P) (δ * conePlus P A) = (2 : ℤ) • (δ * conePlus P A) ∧
    comm (invS P) (δ * coneMinus P C) = -((2 : ℤ) • (δ * coneMinus P C)) := by
  dsimp
  have hLeft := genV_defect_iterates_left_projection hP A C 1
  have hRight := genV_defect_iterates_right_projection hP A C 1
  have hLeft' : P * idempotencyDefect (genV P A C) =
      idempotencyDefect (qgtPlus P A C) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hLeft
  have hRight' : idempotencyDefect (genV P A C) * P =
      idempotencyDefect (qgtPlus P A C) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hRight
  have hPδ : P * idempotencyDefect (genV P A C) =
      idempotencyDefect (genV P A C) * P := hLeft'.trans hRight'.symm
  have hSδ : invS P * idempotencyDefect (genV P A C) =
      idempotencyDefect (genV P A C) * invS P := by
    dsimp [invS]
    noncomm_ring [hPδ]
  have hPlus : comm (invS P) (conePlus P A) = (2 : ℤ) • conePlus P A := by
    peirce_nf hP
  have hMinus : comm (invS P) (coneMinus P C) = -((2 : ℤ) • coneMinus P C) := by
    peirce_nf hP
  constructor
  · unfold comm at hPlus ⊢
    calc
      invS P * (idempotencyDefect (genV P A C) * conePlus P A) -
          idempotencyDefect (genV P A C) * conePlus P A * invS P =
        (invS P * idempotencyDefect (genV P A C)) * conePlus P A -
          idempotencyDefect (genV P A C) * (conePlus P A * invS P) := by
            noncomm_ring
      _ = (idempotencyDefect (genV P A C) * invS P) * conePlus P A -
          idempotencyDefect (genV P A C) * (conePlus P A * invS P) := by rw [hSδ]
      _ = idempotencyDefect (genV P A C) *
          (invS P * conePlus P A - conePlus P A * invS P) := by noncomm_ring
      _ = (2 : ℤ) • (idempotencyDefect (genV P A C) * conePlus P A) := by
          rw [hPlus]
          simp only [mul_smul_comm]
  · unfold comm at hMinus ⊢
    calc
      invS P * (idempotencyDefect (genV P A C) * coneMinus P C) -
          idempotencyDefect (genV P A C) * coneMinus P C * invS P =
        (invS P * idempotencyDefect (genV P A C)) * coneMinus P C -
          idempotencyDefect (genV P A C) * (coneMinus P C * invS P) := by
            noncomm_ring
      _ = (idempotencyDefect (genV P A C) * invS P) * coneMinus P C -
          idempotencyDefect (genV P A C) * (coneMinus P C * invS P) := by rw [hSδ]
      _ = idempotencyDefect (genV P A C) *
          (invS P * coneMinus P C - coneMinus P C * invS P) := by noncomm_ring
      _ = -((2 : ℤ) • (idempotencyDefect (genV P A C) * coneMinus P C)) := by
          rw [hMinus]
          simp only [mul_neg, mul_smul_comm]

/-- The curvature double-commutator mismatches are precisely the operator-valued
idempotency defect acting on the `Φ` and `J` modes. Their Peirce expansion
retains both directed cone channels. -/
theorem idempotency_defect_generates_extreme_peirce_anomaly
    {P : B} (hP : P * P = P) (A C : B) :
    let δ := idempotencyDefect (genV P A C)
    comm δ (conePlus P A) = 0 ∧
    comm δ (coneMinus P C) = 0 ∧
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      -((4 : ℤ) • (δ * conePlus P A + δ * coneMinus P C)) ∧
    derivSqSig P A C (genJ P A C) - derivSqPhi P A C (genJ P A C) =
      -((4 : ℤ) • (δ * conePlus P A - δ * coneMinus P C)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (qgt_defect_iterate_sum_commutes_with_cones hP A C 1).1
    have hsum : comm (conePlus P A)
        (idempotencyDefect (qgtPlus P A C) +
          idempotencyDefect (qgtMinus P A C)) = 0 := by
      simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using h
    have h := hsum
    rw [← genV_defect_cycle_split hP A C] at h
    unfold comm at h ⊢
    calc
      idempotencyDefect (genV P A C) * conePlus P A -
          conePlus P A * idempotencyDefect (genV P A C) =
        -(conePlus P A * idempotencyDefect (genV P A C) -
          idempotencyDefect (genV P A C) * conePlus P A) := by noncomm_ring
      _ = 0 := by rw [h]; simp
  · have h := (qgt_defect_iterate_sum_commutes_with_cones hP A C 1).2
    have hsum : comm (coneMinus P C)
        (idempotencyDefect (qgtPlus P A C) +
          idempotencyDefect (qgtMinus P A C)) = 0 := by
      simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using h
    have h := hsum
    rw [← genV_defect_cycle_split hP A C] at h
    unfold comm at h ⊢
    calc
      idempotencyDefect (genV P A C) * coneMinus P C -
          coneMinus P C * idempotencyDefect (genV P A C) =
        -(coneMinus P C * idempotencyDefect (genV P A C) -
          idempotencyDefect (genV P A C) * coneMinus P C) := by noncomm_ring
      _ = 0 := by rw [h]; simp
  · rw [defect_deriv_sig_sub_j hP A C]
    simp only [genPhi, zsmul_add]
    noncomm_ring
  · rw [defect_deriv_sig_sub_phi hP A C]
    simp only [genJ, zsmul_sub]
    noncomm_ring

/-- The D₃₇ logistic variance is the negative idempotency defect, so it generates
the same two Peirce-channel curvature mismatches with the corresponding sign
reversal. Both directed boundary cones remain explicit in the formulas. -/
theorem logistic_variance_generates_extreme_peirce_anomaly
    {P : B} (hP : P * P = P) (A C : B) :
    comm (NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C)
        (conePlus P A) = 0 ∧
    comm (NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C)
        (coneMinus P C) = 0 ∧
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      (4 : ℤ) •
        (NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * conePlus P A +
         NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * coneMinus P C) ∧
    derivSqSig P A C (genJ P A C) - derivSqPhi P A C (genJ P A C) =
      (4 : ℤ) •
        (NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * conePlus P A -
         NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * coneMinus P C) := by
  have hLogistic :
      NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C =
        -idempotencyDefect (genV P A C) := by
    simpa only [NonCommutativeOperatorTimePoset.idemDefect, idempotencyDefect] using
      (NonCommutativeItFromBitLogisticPoset.logistic_bit_variance_and_defect_equivalence
        hP A C).2.2.2
  rcases idempotency_defect_generates_extreme_peirce_anomaly hP A C with
    ⟨hPlusComm, hMinusComm, hPhi, hJ⟩
  have hDefect : idempotencyDefect (genV P A C) =
      -NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C := by
    rw [hLogistic]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hLogistic]
    unfold comm at hPlusComm ⊢
    have hEq := sub_eq_zero.mp hPlusComm
    simp only [neg_mul, mul_neg, sub_neg_eq_add]
    rw [hEq]
    simp
  · rw [hLogistic]
    unfold comm at hMinusComm ⊢
    have hEq := sub_eq_zero.mp hMinusComm
    simp only [neg_mul, mul_neg, sub_neg_eq_add]
    rw [hEq]
    simp
  · calc
      derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
        -((4 : ℤ) • (idempotencyDefect (genV P A C) * conePlus P A +
          idempotencyDefect (genV P A C) * coneMinus P C)) := hPhi
      _ = (4 : ℤ) •
          (NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * conePlus P A +
           NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * coneMinus P C) := by
        rw [hDefect]
        simp only [neg_mul, neg_add, neg_zsmul]
        abel_nf
  · calc
      derivSqSig P A C (genJ P A C) - derivSqPhi P A C (genJ P A C) =
        -((4 : ℤ) • (idempotencyDefect (genV P A C) * conePlus P A -
          idempotencyDefect (genV P A C) * coneMinus P C)) := hJ
      _ = (4 : ℤ) •
          (NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * conePlus P A -
           NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C * coneMinus P C) := by
        rw [hDefect]
        simp only [neg_mul, neg_sub, neg_zsmul]
        abel_nf

end InfoGeometry.OperatorAlgebra.PeirceSpine
