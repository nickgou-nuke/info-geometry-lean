/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockAdjoint
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Coordinate Fock contraction bounds on the actual real metric

CAR and the proved inner-adjoint identity supply the bounds; no completeness.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- Coordinate CAR splits the squared norm into creation and contraction parts. -/
theorem fock_coordinate_norm_sq_split (n : ℕ) (i : Fin n)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    ‖extAction ((Pi.basisFun ℝ (Fin n)) i) x‖ ^ 2 +
      ‖intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) x‖ ^ 2 = ‖x‖ ^ 2 := by
  let C := extAction ((Pi.basisFun ℝ (Fin n)) i)
  let D := intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))
  have hc : C (D x) + D (C x) = x := by
    have h := ext_int_anticommutator ((Pi.basisFun ℝ (Fin n)) i)
      (LinearMap.proj i : Module.Dual ℝ (Vector n)) x
    have heval : (LinearMap.proj i : Module.Dual ℝ (Vector n))
        ((Pi.basisFun ℝ (Fin n)) i) = 1 := by simp
    rw [heval, map_one, one_mul] at h
    exact h
  have hleft : inner ℝ (C (D x)) x = ‖D x‖ ^ 2 := by
    calc
      _ = inner ℝ (D x) (D x) := fock_extAction_intAction_inner n i (D x) x
      _ = _ := real_inner_self_eq_norm_sq _
  have hright : inner ℝ (D (C x)) x = ‖C x‖ ^ 2 := by
    calc
      _ = inner ℝ x (D (C x)) := real_inner_comm _ _
      _ = inner ℝ (C x) (C x) := (fock_extAction_intAction_inner n i x (C x)).symm
      _ = _ := real_inner_self_eq_norm_sq _
  have hp := congrArg (fun y => inner ℝ y x) hc
  rw [inner_add_left, hleft, hright, real_inner_self_eq_norm_sq] at hp
  simpa only [C, D, add_comm] using hp

/-- Native coordinate creation is contractive for the induced real Fock norm. -/
theorem fock_extAction_norm_le (n : ℕ) (i : Fin n)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    ‖extAction ((Pi.basisFun ℝ (Fin n)) i) x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ ≤ ‖extAction ((Pi.basisFun ℝ (Fin n)) i) x‖ ^ 2 +
        ‖intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) x‖ ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    _ = _ := fock_coordinate_norm_sq_split n i x

/-- Native coordinate contraction is contractive for the same real Fock norm. -/
theorem fock_intAction_norm_le (n : ℕ) (i : Fin n)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    ‖intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ ≤ ‖extAction ((Pi.basisFun ℝ (Fin n)) i) x‖ ^ 2 +
        ‖intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) x‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    _ = _ := fock_coordinate_norm_sq_split n i x

/-- The existing coordinate creation map, now continuous by its proved bound. -/
def fockExtActionCLM (n : ℕ) (i : Fin n) :
    InfoGeometry.Clifford.SpinorSpace (Vector n) →L[ℝ]
      InfoGeometry.Clifford.SpinorSpace (Vector n) :=
  (extAction ((Pi.basisFun ℝ (Fin n)) i)).mkContinuous 1
    (fun x => by simpa only [one_mul] using fock_extAction_norm_le n i x)

/-- The existing coordinate contraction map, now continuous by its proved bound. -/
def fockIntActionCLM (n : ℕ) (i : Fin n) :
    InfoGeometry.Clifford.SpinorSpace (Vector n) →L[ℝ]
      InfoGeometry.Clifford.SpinorSpace (Vector n) :=
  (intAction (LinearMap.proj i : Module.Dual ℝ (Vector n))).mkContinuous 1
    (fun x => by simpa only [one_mul] using fock_intAction_norm_le n i x)

@[simp] theorem fockExtActionCLM_apply (n : ℕ) (i : Fin n)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockExtActionCLM n i x = extAction ((Pi.basisFun ℝ (Fin n)) i) x := rfl

@[simp] theorem fockIntActionCLM_apply (n : ℕ) (i : Fin n)
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockIntActionCLM n i x =
      intAction (LinearMap.proj i : Module.Dual ℝ (Vector n)) x := rfl

/-- The continuous creation operator has norm at most one. -/
theorem fockExtActionCLM_norm_le (n : ℕ) (i : Fin n) :
    ‖fockExtActionCLM n i‖ ≤ 1 := by
  unfold fockExtActionCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The continuous contraction operator has norm at most one. -/
theorem fockIntActionCLM_norm_le (n : ℕ) (i : Fin n) :
    ‖fockIntActionCLM n i‖ ≤ 1 := by
  unfold fockIntActionCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
