import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.ModularRotorFlow

/-- Coordinate-free modular rotor data. -/
structure ModularRotor (A : Type*) [Ring A] where
  rotor : ℝ → A
  rotorInv : ℝ → A
  mul_inv : ∀ t, rotor t * rotorInv t = 1
  inv_mul : ∀ t, rotorInv t * rotor t = 1
  hom : ∀ t1 t2, rotor (t1 + t2) = rotor t1 * rotor t2
  hom_inv : ∀ t1 t2, rotorInv (t1 + t2) = rotorInv t2 * rotorInv t1

/-- Coordinate-free modular flow by rotor conjugation. -/
def modular_flow_act {A : Type*} [Ring A] (M : ModularRotor A) (t : ℝ) (X : A) : A :=
  M.rotor t * X * M.rotorInv t

/-- The modular flow is a 1-parameter group action. -/
theorem modular_flow_group_action {A : Type*} [Ring A]
    (M : ModularRotor A) (t1 t2 : ℝ) (X : A) :
    modular_flow_act M (t1 + t2) X = modular_flow_act M t1 (modular_flow_act M t2 X) := by
  unfold modular_flow_act
  rw [M.hom, M.hom_inv]
  simp only [mul_assoc]

/-- Trace-class functional on the operator space. -/
structure TraceFunctional (A : Type*) [Ring A] where
  tau : A → ℝ
  map_add : ∀ x y : A, tau (x + y) = tau x + tau y
  map_sub : ∀ x y : A, tau (x - y) = tau x - tau y
  map_cyclic : ∀ x y : A, tau (x * y) = tau (y * x)

/-- Real algebra trace compatibility. -/
class TraceAlgebra (A : Type*) [Ring A] [Algebra ℝ A] (F : TraceFunctional A) where
  map_scale : ∀ (c : ℝ) (x : A), F.tau ((algebraMap ℝ A c) * x) = c * F.tau x

/-- The commutator bracket: `[H, X] = H * X - X * H`. -/
def modularCommutator {A : Type*} [Ring A] (H X : A) : A :=
  H * X - X * H

/-- The modular eigenvalue/eigenstate relation. -/
def isEigenstate {A : Type*} [Ring A] [Algebra ℝ A] (H X : A) (lam : ℝ) : Prop :=
  modularCommutator H X = (algebraMap ℝ A lam) * X

/-- The trace of a commutator vanishes by cyclicity. -/
theorem trace_commutator_zero {A : Type*} [Ring A] (F : TraceFunctional A) (H X : A) :
    F.tau (modularCommutator H X) = 0 := by
  unfold modularCommutator
  rw [F.map_sub]
  have h_cyc : F.tau (H * X) = F.tau (X * H) := F.map_cyclic H X
  rw [h_cyc]
  ring

/-- Modular spectral selection: nonzero eigenvalue forces zero expectation. -/
theorem modular_spectral_selection_rule {A : Type*} [Ring A] [Algebra ℝ A]
    (F : TraceFunctional A) [TraceAlgebra A F] (H X : A) (lam : ℝ)
    (h_eigen : isEigenstate H X lam) (h_nonzero : lam ≠ 0) :
    F.tau X = 0 := by
  have h_tr := trace_commutator_zero F H X
  unfold isEigenstate at h_eigen
  rw [h_eigen] at h_tr
  rw [TraceAlgebra.map_scale lam X] at h_tr
  have h' : lam * F.tau X = 0 := by
    simpa [mul_comm] using h_tr
  exact (mul_eq_zero.mp h').resolve_left h_nonzero

end InfoGeometry.Canonical.ModularRotorFlow
