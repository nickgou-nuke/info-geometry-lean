/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockCompletedSameModeCAR
import InfoGeometry.Clifford.FiniteFockRotorShear
import InfoGeometry.Canonical.StreamSixOrbitComparison

/-! Actual completed Fock operators realize existing rotor and pole constructions.
Uncompiled sandbox. No new carrier or action; hyperbolic unitarity is not asserted. -/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
open InfoGeometry.Canonical.ReflexiveRotorRealTime
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace
attribute [local instance] fockInfinityInnerProductCore fockInfinityPreInnerProductCore
  fockInfinityNormedAddCommGroup fockInfinityInnerProductSpace fockInfinityNormedSpace
  fockInfinityUniformContinuousConstSMul fockInfinityMetricUniformSpace fockInfinityMetricTopology

variable (m : ℕ) (i : Fin m)
local notation "D" => fockCompletedContractionCLM m i
local notation "C" => fockCompletedCreationCLM m i

theorem fockCompletedContraction_reflexive : D * C * D = D := by
  have h := congrArg (fun T => T * D) (fockCompleted_sameMode_CAR m i)
  simpa only [add_mul, mul_assoc, fockCompletedContractionCLM_sq_zero,
    mul_zero, add_zero, one_mul] using h

theorem fockCompletedCreation_reflexive : C * D * C = C := by
  have h := congrArg (fun T => T * C) (fockCompleted_sameMode_CAR m i)
  simpa only [add_mul, mul_assoc, fockCompletedCreationCLM_sq_zero,
    mul_zero, zero_add, one_mul] using h

/-- Every primitive field of the existing Stream5 interface comes from native CAR. -/
theorem fockCompleted_isDualSeedPair : IsDualSeedPair D C where
  d_sq := fockCompletedContractionCLM_sq_zero m i
  B_sq := fockCompletedCreationCLM_sq_zero m i
  dBd := fockCompletedContraction_reflexive m i
  BdB := fockCompletedCreation_reflexive m i

theorem fockCompleted_carrierSupport : carrierSupport D C = 1 :=
  fockCompleted_sameMode_CAR m i

theorem fockCompleted_polePlus_idempotent : (D * C) * (D * C) = D * C := by
  rw [← mul_assoc, fockCompletedContraction_reflexive]

theorem fockCompleted_poleMinus_idempotent : (C * D) * (C * D) = C * D := by
  rw [← mul_assoc, fockCompletedCreation_reflexive]

/-- These are Hilbert self-adjoint projections, not merely ring idempotents. -/
theorem fockCompleted_polePlus_selfAdjoint : IsSelfAdjoint (D * C) := by
  change star (D * C) = D * C
  simp only [star_mul, ContinuousLinearMap.star_eq_adjoint,
    fockCompletedCreationCLM_adjoint, fockCompletedContractionCLM_adjoint]

theorem fockCompleted_poleMinus_selfAdjoint : IsSelfAdjoint (C * D) := by
  change star (C * D) = C * D
  simp only [star_mul, ContinuousLinearMap.star_eq_adjoint,
    fockCompletedCreationCLM_adjoint, fockCompletedContractionCLM_adjoint]

/-- The full support removes the inactive complement in the existing rotor. -/
theorem fockCompleted_realRotor_eq (t : ℝ) :
    realRotor D C t = Real.cos t • 1 + Real.sin t • (D - C) := by
  simp only [realRotor, InfoGeometry.Canonical.ReflexiveNilpotentFlows.rotor,
    InfoGeometry.Canonical.ReflexiveNilpotentFlows.complement,
    InfoGeometry.Canonical.ReflexiveNilpotentFlows.support,
    fockCompleted_sameMode_CAR, sub_self, zero_add]

theorem fockCompleted_realRotor_apply (t : ℝ) (x : RealFockCompletion) :
    realRotor D C t x = Real.cos t • x + Real.sin t • (D x - C x) := by
  rw [fockCompleted_realRotor_eq]
  rfl

/-- The completed rotor restricts to the actual finite rotor at every later stage. -/
theorem fockCompleted_realRotor_stage (n : ℕ) (h : m ≤ n) (t : ℝ) (x : FockStage n) :
    realRotor D C t (fockStageToCompletion n x) =
      fockStageToCompletion n
        (realRotor (fockIntActionCLM n (fockModeShift m n h i))
          (fockExtActionCLM n (fockModeShift m n h i)) t x) := by
  rw [fockCompleted_realRotor_apply, fock_realRotor_apply,
    fockCompletedContractionCLM_stage m n h, fockCompletedCreationCLM_stage m n h]
  simp only [map_add, map_smul, map_sub]

/-- Direct quadratic moving-pole action on every original completed vector. -/
theorem fockCompleted_movingPolePlus_apply (c s : ℝ) (x : RealFockCompletion) :
    movingPolePlus c s D C x =
      (c*c) • D (C x) + (s*s) • C (D x) - (c*s) • (D x + C x) := by
  rw [movingPolePlus_eq (fockCompleted_isDualSeedPair m i)]
  rfl

theorem fockCompleted_movingPolePlus_idempotent (t : ℝ) :
    movingPolePlus (Real.cos t) (Real.sin t) D C *
      movingPolePlus (Real.cos t) (Real.sin t) D C =
        movingPolePlus (Real.cos t) (Real.sin t) D C := by
  apply movingPolePlus_idem (fockCompleted_isDualSeedPair m i)
  simpa only [pow_two] using Real.cos_sq_add_sin_sq t

/-- The elliptic polynomial is genuinely self-adjoint for real coefficients. -/
theorem fockCompleted_movingPolePlus_selfAdjoint (c s : ℝ) :
    IsSelfAdjoint (movingPolePlus c s D C) := by
  change star (movingPolePlus c s D C) = movingPolePlus c s D C
  rw [movingPolePlus_eq (fockCompleted_isDualSeedPair m i)]
  simp only [polePlus, poleMinus, transitionVelocity, star_sub, star_add,
    star_smul, star_trivial, star_mul, ContinuousLinearMap.star_eq_adjoint,
    fockCompletedCreationCLM_adjoint, fockCompletedContractionCLM_adjoint,
    add_comm C D]

/-- The moving completed pole reads back to the finite trajectory, not a new action. -/
theorem fockCompleted_movingPolePlus_stage (n : ℕ) (h : m ≤ n) (t : ℝ)
    (x : FockStage n) :
    movingPolePlus (Real.cos t) (Real.sin t) D C (fockStageToCompletion n x) =
      fockStageToCompletion n (movingPolePlus (Real.cos t) (Real.sin t)
        (fockIntActionCLM n (fockModeShift m n h i))
        (fockExtActionCLM n (fockModeShift m n h i)) x) := by
  rw [fockCompleted_movingPolePlus_apply, fock_movingPolePlus_apply]
  simp only [fockCompletedContractionCLM_stage m n h,
    fockCompletedCreationCLM_stage m n h, map_add, map_sub, map_smul]

/-- Actual Stream6 conjugation readback; no inverse or unitary claim without premises. -/
theorem fockCompleted_hyperbolicPlus_apply (u v : ℝ) (x : RealFockCompletion) :
    InfoGeometry.Canonical.ComplementHyperbolicOrbit.hyperbolicPlus u v D C x =
      (u*u) • D (C x) - (v*v) • C (D x) - (u*v) • (D x - C x) := by
  rw [InfoGeometry.Canonical.StreamSixOrbitComparison.hyperbolicPlus_eq_stream6
    (fockCompleted_isDualSeedPair m i)]
  rfl

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
