/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockNormBounds
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis

/-! Actual coordinate Fock CLMs satisfy CAR and the existing reflexive-pair interfaces.
Sandbox candidate: uncompiled. Only the existing real Fock metric is activated locally. -/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

variable (n : ℕ) (i : Fin n)

theorem fockIntActionCLM_sq_zero :
    fockIntActionCLM n i * fockIntActionCLM n i = 0 := by
  ext x
  exact int_sq_zero (LinearMap.proj i : Module.Dual ℝ (Vector n)) x

theorem fockExtActionCLM_sq_zero :
    fockExtActionCLM n i * fockExtActionCLM n i = 0 := by
  ext x
  exact ext_sq_zero ((Pi.basisFun ℝ (Fin n)) i) x

/-- The active unit is the identity on the entire existing spinor space. -/
theorem fock_coordinate_CLM_CAR :
    fockIntActionCLM n i * fockExtActionCLM n i +
      fockExtActionCLM n i * fockIntActionCLM n i = 1 := by
  ext x
  change intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
      (extAction ((Pi.basisFun ℝ (Fin n)) i) x) +
    extAction ((Pi.basisFun ℝ (Fin n)) i)
      (intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) x) = x
  have h := ext_int_anticommutator ((Pi.basisFun ℝ (Fin n)) i)
    (LinearMap.proj i : Module.Dual ℝ (Vector n)) x
  have heval : (LinearMap.proj i : Module.Dual ℝ (Vector n))
      ((Pi.basisFun ℝ (Fin n)) i) = 1 := by simp
  rw [heval, map_one, one_mul] at h
  simpa only [add_comm] using h

theorem fockIntActionCLM_reflexive :
    fockIntActionCLM n i * fockExtActionCLM n i * fockIntActionCLM n i =
      fockIntActionCLM n i := by
  have h := congrArg (fun T => T * fockIntActionCLM n i) (fock_coordinate_CLM_CAR n i)
  simpa only [add_mul, mul_assoc, fockIntActionCLM_sq_zero, mul_zero,
    add_zero, one_mul] using h

theorem fockExtActionCLM_reflexive :
    fockExtActionCLM n i * fockIntActionCLM n i * fockExtActionCLM n i =
      fockExtActionCLM n i := by
  have h := congrArg (fun T => T * fockExtActionCLM n i) (fock_coordinate_CLM_CAR n i)
  simpa only [add_mul, mul_assoc, fockExtActionCLM_sq_zero, mul_zero,
    zero_add, one_mul] using h

/-- Existing Stream5 interface, with every primitive relation derived above. -/
theorem fock_isDualSeedPair :
    InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.IsDualSeedPair
      (fockIntActionCLM n i) (fockExtActionCLM n i) where
  d_sq := fockIntActionCLM_sq_zero n i
  B_sq := fockExtActionCLM_sq_zero n i
  dBd := fockIntActionCLM_reflexive n i
  BdB := fockExtActionCLM_reflexive n i

/-- Existing Stream4 interface on precisely the same two operators. -/
theorem fock_isDualRootOfZeroPair :
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.IsDualRootOfZeroPair
      (fockIntActionCLM n i) (fockExtActionCLM n i) where
  d_sq := fockIntActionCLM_sq_zero n i
  B_sq := fockExtActionCLM_sq_zero n i
  dBd := fockIntActionCLM_reflexive n i
  BdB := fockExtActionCLM_reflexive n i

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
