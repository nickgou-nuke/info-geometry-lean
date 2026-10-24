/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteFockCLMReflexivePair

/-!
# Chordal displacement in the actual finite real Fock norm

The native inner adjoint identity supplies symmetry; the existing algebraic
chordal square and CAR then give an exact norm on every original spinor.
No completeness or supplied self-adjointness premise is used.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

variable (n : ℕ) (i : Fin n)
local notation "D" => fockIntActionCLM n i
local notation "C" => fockExtActionCLM n i

/-- Reverse inner adjointness is derived using the real inner symmetry. -/
theorem fock_intActionCLM_extActionCLM_inner (x y : SpinorSpace (Vector n)) :
    inner ℝ (D x) y = inner ℝ x (C y) := by
  calc
    _ = inner ℝ y (D x) := real_inner_comm _ _
    _ = inner ℝ (C y) x := (fock_extAction_intAction_inner n i y x).symm
    _ = _ := real_inner_comm _ _

/-- Symmetry of the actual plus pole. -/
theorem fock_plusPole_inner (x y : SpinorSpace (Vector n)) :
    inner ℝ (D (C x)) y = inner ℝ x (D (C y)) := by
  calc
    _ = inner ℝ (C x) (C y) := fock_intActionCLM_extActionCLM_inner n i (C x) y
    _ = _ := fock_extAction_intAction_inner n i x (C y)

/-- Symmetry of the actual opposite pole. -/
theorem fock_minusPole_inner (x y : SpinorSpace (Vector n)) :
    inner ℝ (C (D x)) y = inner ℝ x (C (D y)) := by
  calc
    _ = inner ℝ (D x) (D y) := fock_extAction_intAction_inner n i (D x) y
    _ = _ := fock_intActionCLM_extActionCLM_inner n i x (D y)

/-- The coordinate creation/contraction sum is symmetric in the native metric. -/
theorem fock_velocity_inner (x y : SpinorSpace (Vector n)) :
    inner ℝ (D x + C x) y = inner ℝ x (D y + C y) := by
  rw [inner_add_left, inner_add_right,
    fock_intActionCLM_extActionCLM_inner n i x y]
  have h : inner ℝ (C x) y = inner ℝ x (D y) :=
    fock_extAction_intAction_inner n i x y
  rw [h, add_comm]

/-- Symmetry follows from the actual moving-pole polynomial for all real coefficients. -/
theorem fock_movingPolePlus_inner (c s : ℝ) (x y : SpinorSpace (Vector n)) :
    inner ℝ (movingPolePlus c s D C x) y = inner ℝ x (movingPolePlus c s D C y) := by
  rw [movingPolePlus_eq (fock_isDualSeedPair n i) c s]
  change inner ℝ ((c*c) • D (C x) + (s*s) • C (D x) - (c*s) • (D x+C x)) y =
    inner ℝ x ((c*c) • D (C y) + (s*s) • C (D y) - (c*s) • (D y+C y))
  calc
    _ = (c*c)*inner ℝ (D (C x)) y + (s*s)*inner ℝ (C (D x)) y -
        (c*s)*inner ℝ (D x+C x) y := by
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    _ = (c*c)*inner ℝ x (D (C y)) + (s*s)*inner ℝ x (C (D y)) -
        (c*s)*inner ℝ x (D y+C y) := by
      rw [fock_plusPole_inner, fock_minusPole_inner, fock_velocity_inner]
    _ = _ := by
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right]

/-- The displacement is symmetric; no circle equation is needed for this inner law. -/
theorem fock_chordalDisplacement_inner (c s : ℝ) (x y : SpinorSpace (Vector n)) :
    inner ℝ ((movingPolePlus c s D C - D*C) x) y =
      inner ℝ x ((movingPolePlus c s D C - D*C) y) := by
  change inner ℝ (movingPolePlus c s D C x-D (C x)) y =
    inner ℝ x (movingPolePlus c s D C y-D (C y))
  rw [inner_sub_left, inner_sub_right, fock_movingPolePlus_inner, fock_plusPole_inner]

/-- Native CAR turns the existing support-valued chordal square into the full identity. -/
theorem fock_chordalDisplacement_sq (c s : ℝ) (hc : c*c+s*s=1) :
    (movingPolePlus c s D C-D*C)*(movingPolePlus c s D C-D*C) = (s*s) • 1 := by
  have h := (movingPolePlus_chordal_square_and_compression (fock_isDualSeedPair n i) hc).1
  change (movingPolePlus c s D C-D*C)*(movingPolePlus c s D C-D*C) =
    (s*s) • (D*C+C*D) at h
  rw [fock_coordinate_CLM_CAR] at h
  exact h

/-- Squared norm of the displacement on every actual finite Fock vector. -/
theorem fock_chordalDisplacement_norm_sq (c s : ℝ) (hc : c*c+s*s=1)
    (x : SpinorSpace (Vector n)) :
    ‖(movingPolePlus c s D C-D*C) x‖ ^ 2 = (s*s)*‖x‖^2 := by
  let E := movingPolePlus c s D C-D*C
  have hE : E (E x) = (s*s) • x := by
    have h := congrArg (fun T : SpinorSpace (Vector n) →L[ℝ] SpinorSpace (Vector n) => T x)
      (fock_chordalDisplacement_sq n i c s hc)
    exact h
  change ‖E x‖^2 = (s*s)*‖x‖^2
  calc
    _ = inner ℝ (E x) (E x) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x (E (E x)) := fock_chordalDisplacement_inner n i c s x (E x)
    _ = inner ℝ x ((s*s) • x) := congrArg (inner ℝ x) hE
    _ = _ := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- Exact displacement norm, including zero coefficients and the zero vector. -/
theorem fock_chordalDisplacement_norm (c s : ℝ) (hc : c*c+s*s=1)
    (x : SpinorSpace (Vector n)) :
    ‖(movingPolePlus c s D C-D*C) x‖ = |s|*‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg s) (norm_nonneg x))).mp
  rw [mul_pow, sq_abs, fock_chordalDisplacement_norm_sq n i c s hc, pow_two s]

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
