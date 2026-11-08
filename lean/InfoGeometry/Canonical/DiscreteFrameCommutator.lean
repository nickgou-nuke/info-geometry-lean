/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing

/-!
# A signed discrete frame commutator

X and Z are involutions, not quaternion generators or unipotents.
The four-factor word is an algebraic commutator since both inverses equal
the generators. This file does not construct geometric holonomy or a group-H²
classification. The nonidentity theorem explicitly excludes characteristic two.
-/

namespace InfoGeometry.Canonical.DiscreteFrameCommutator

variable (A : Type*) [Ring A]

def frameX : Matrix (Fin 4) (Fin 4) A :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

def frameZ : Matrix (Fin 4) (Fin 4) A :=
  !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0]

theorem frameX_sq : frameX A * frameX A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [frameX, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem frameZ_sq : frameZ A * frameZ A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [frameZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem frame_anticommute : frameZ A * frameX A = -(frameX A * frameZ A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [frameX, frameZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem frame_commutator :
    frameX A * frameZ A * frameX A * frameZ A = -1 := by
  calc
    _ = frameX A * (frameZ A * frameX A) * frameZ A := by noncomm_ring
    _ = frameX A * (-(frameX A * frameZ A)) * frameZ A := by rw [frame_anticommute]
    _ = -((frameX A * frameX A) * (frameZ A * frameZ A)) := by noncomm_ring
    _ = -1 := by rw [frameX_sq, frameZ_sq]; simp

theorem frame_commutator_ne_one (hchar : (-1 : A) ≠ 1) :
    frameX A * frameZ A * frameX A * frameZ A ≠ 1 := by
  rw [frame_commutator]
  intro h
  apply hchar
  simpa using congrArg (fun M : Matrix (Fin 4) (Fin 4) A => M 0 0) h

/-- The sign is witnessed by genuinely noncommuting operators. -/
theorem frame_not_commute (hchar : (-1 : A) ≠ 1) :
    frameX A * frameZ A ≠ frameZ A * frameX A := by
  intro h
  apply frame_commutator_ne_one A hchar
  calc
    _ = frameX A * (frameZ A * frameX A) * frameZ A := by noncomm_ring
    _ = frameX A * (frameX A * frameZ A) * frameZ A := by rw [← h]
    _ = (frameX A * frameX A) * (frameZ A * frameZ A) := by noncomm_ring
    _ = 1 := by rw [frameX_sq, frameZ_sq]; simp

/-- A characteristic assumption supplies a closed noncommutativity witness. -/
theorem frame_not_commute_of_neZero_two [@NeZero A _ 2] :
    frameX (A := A) * frameZ (A := A) ≠ frameZ (A := A) * frameX (A := A) := by
  apply frame_not_commute A
  intro h
  have hz : (2 : A) = 0 := by
    simpa only [neg_add_cancel, one_add_one_eq_two] using
      (congrArg (fun x : A => x + 1) h).symm
  exact NeZero.ne (2 : A) hz

/-- Rephasing the generators and their inverses by central real units
does not remove the commutator sign. -/
theorem rephased_frame_commutator (a b : ℝˣ) :
    ((a : ℝ) • frameX ℝ) * ((b : ℝ) • frameZ ℝ) *
        ((↑(a⁻¹) : ℝ) • frameX ℝ) * ((↑(b⁻¹) : ℝ) • frameZ ℝ) = -1 := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : (↑(b⁻¹) : ℝ) * ((↑(a⁻¹) : ℝ) * ((b : ℝ) * (a : ℝ))) = 1 := by
    calc
      _ = ((a : ℝ) * ↑(a⁻¹)) * ((b : ℝ) * ↑(b⁻¹)) := by ring
      _ = 1 := by simp
  rw [h, one_smul, frame_commutator]

end InfoGeometry.Canonical.DiscreteFrameCommutator
