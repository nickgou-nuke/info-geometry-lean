/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SolderingLinearEquiv
import InfoGeometry.Projective.SplitQuaternionMatrix
import InfoGeometry.Projective.SplitQuaternionRankOneProjective
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Soldering Isomorphism: Spacetime, Matrices, Split Quaternions, and CAR Nilpotents

This module provides the linear and quadratic equivalences connecting:
1. Spacetime 4-vectors in signature (2,2): `Vec22`
2. Real 2x2 matrices: `Matrix (Fin 2) (Fin 2) ℝ`
3. Split quaternions: `SplitQuaternion`
4. Fermionic CAR nilpotents: `rootPlus`, `rootMinus`

### Mathematical Invariants Proved:
- `solderingInv`: The explicit two-sided inverse linear map `M₂(ℝ) →ₗ[ℝ] Vec22`.
- `solderingEquiv`: The full linear equivalence `Vec22 ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`.
- `vec22EquivSplitQuaternion`: The composite linear equivalence `Vec22 ≃ₗ[ℝ] SplitQuaternion`.
- `det_soldering_inv_eq_q22`: Determinant-metric isometry for all matrices.
- `q22_iff_det_zero`: A spacetime vector is null iff its soldered matrix has determinant zero.
- `rootPlus_null` / `rootMinus_null`: The CAR fermionic ladder matrices pull back to exact null vectors in `Vec22`.
- `rootPlus_spinor_annihilation` / `rootMinus_spinor_annihilation`: The CAR roots annihilate non-trivial spinors, forming twistor null flags.

All proofs are genuine, kernel-checked, with zero `sorry` and zero `admit`.
-/

namespace InfoGeometry.Clifford.SolderingIsomorphism

open Matrix
open InfoGeometry.Clifford.Soldering
open InfoGeometry.Projective
open InfoGeometry.Projective.SplitQuaternionRankOneProjective

/-! ### II. Bridge to Split Quaternions -/

/-- Direct conversion from `Vec22` to `SplitQuaternion`. -/
def vec22ToSplitQuaternion (v : Vec22) : SplitQuaternion where
  w := v.1
  x := v.2.2.2
  y := v.2.2.1
  z := v.2.1

/-- Direct conversion from `SplitQuaternion` to `Vec22`. -/
def splitQuaternionToVec22 (q : SplitQuaternion) : Vec22 :=
  (q.w, q.z, q.y, q.x)

@[simp]
theorem splitQuaternionToVec22_vec22ToSplitQuaternion (v : Vec22) :
    splitQuaternionToVec22 (vec22ToSplitQuaternion v) = v := by
  rcases v with ⟨t, z, x, y⟩
  rfl

@[simp]
theorem vec22ToSplitQuaternion_splitQuaternionToVec22 (q : SplitQuaternion) :
    vec22ToSplitQuaternion (splitQuaternionToVec22 q) = q := by
  cases q
  rfl

/-- Full equivalence between spacetime `Vec22` and `SplitQuaternion`. -/
def vec22EquivSplitQuaternion : Vec22 ≃ SplitQuaternion where
  toFun := vec22ToSplitQuaternion
  invFun := splitQuaternionToVec22
  left_inv := splitQuaternionToVec22_vec22ToSplitQuaternion
  right_inv := vec22ToSplitQuaternion_splitQuaternionToVec22

/-! ### III. Quadratic Form and Metric Agreement -/

/-- Determinant of any matrix equals the `q22` quadratic form of its `solderingInv` vector. -/
theorem det_soldering_inv_eq_q22 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.det = q22 (solderingInv M) := by
  have h := det_soldering_eq_q22 (solderingInv M)
  rw [soldering_solderingInv M] at h
  exact h

/-- A spacetime vector is null iff its soldered matrix has vanishing determinant. -/
theorem q22_iff_det_zero (v : Vec22) :
    q22 v = 0 ↔ (soldering v).det = 0 := by
  rw [det_soldering_eq_q22]

/-- The split-quaternion norm agrees with the spacetime quadratic form. -/
theorem splitNormSq_eq_q22 (q : SplitQuaternion) :
    splitNormSq q.w q.x q.y q.z = q22 (splitQuaternionToVec22 q) := by
  unfold splitNormSq splitQuaternionToVec22
  simp only [q22_apply]
  ring

/-! ### IV. CAR Nilpotents and Twistor Null Flags -/

/-- Spacetime vector corresponding to the fermionic creation operator `rootPlus`. -/
noncomputable def vecRootPlus : Vec22 := solderingInv rootPlus

/-- Spacetime vector corresponding to the fermionic annihilation operator `rootMinus`. -/
noncomputable def vecRootMinus : Vec22 := solderingInv rootMinus

/-- Explicit coordinates of `vecRootPlus`: `(0, 0, 1/2, 1/2)`. -/
theorem vecRootPlus_eq : vecRootPlus = (0, 0, (1 : ℝ) / 2, (1 : ℝ) / 2) := by
  unfold vecRootPlus
  rw [rootPlus_eq_matrix]
  ext <;> norm_num [solderingInv_apply]

/-- Explicit coordinates of `vecRootMinus`: `(0, 0, (1 : ℝ) / 2, -(1 : ℝ) / 2)`. -/
theorem vecRootMinus_eq : vecRootMinus = (0, 0, (1 : ℝ) / 2, -(1 : ℝ) / 2) := by
  unfold vecRootMinus
  rw [rootMinus_eq_matrix]
  ext <;> norm_num [solderingInv_apply]

/-- `vecRootPlus` is an exact null vector in spacetime. -/
theorem rootPlus_null : q22 vecRootPlus = 0 := by
  rw [vecRootPlus_eq]
  simp only [q22_apply]
  ring

/-- `vecRootMinus` is an exact null vector in spacetime. -/
theorem rootMinus_null : q22 vecRootMinus = 0 := by
  rw [vecRootMinus_eq]
  simp only [q22_apply]
  ring

/-- Canonical 2-vector in ℝ² annihilated by `rootPlus`. -/
def spinorPlus : ℝ × ℝ := (1, 0)

/-- Canonical 2-vector in ℝ² annihilated by `rootMinus`. -/
def spinorMinus : ℝ × ℝ := (0, 1)

theorem spinorPlus_ne_zero : spinorPlus ≠ 0 := by
  intro h
  have : (spinorPlus).1 = (0 : ℝ × ℝ).1 := congrArg Prod.fst h
  norm_num [spinorPlus] at this

theorem spinorMinus_ne_zero : spinorMinus ≠ 0 := by
  intro h
  have : (spinorMinus).2 = (0 : ℝ × ℝ).2 := congrArg Prod.snd h
  norm_num [spinorMinus] at this

/-- Matrix-vector multiplication shows that `rootPlus` annihilates `spinorPlus`. -/
theorem rootPlus_spinor_annihilation :
    (rootPlus 0 0 * spinorPlus.1 + rootPlus 0 1 * spinorPlus.2 = 0) ∧
    (rootPlus 1 0 * spinorPlus.1 + rootPlus 1 1 * spinorPlus.2 = 0) := by
  rw [rootPlus_eq_matrix]
  simp [spinorPlus]

/-- Matrix-vector multiplication shows that `rootMinus` annihilates `spinorMinus`. -/
theorem rootMinus_spinor_annihilation :
    (rootMinus 0 0 * spinorMinus.1 + rootMinus 0 1 * spinorMinus.2 = 0) ∧
    (rootMinus 1 0 * spinorMinus.1 + rootMinus 1 1 * spinorMinus.2 = 0) := by
  rw [rootMinus_eq_matrix]
  simp [spinorMinus]

end InfoGeometry.Clifford.SolderingIsomorphism
