/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import InfoGeometry.Clifford.SplitCl11GradedTensorTower

noncomputable section

open InfoGeometry.Clifford
open InfoGeometry.Clifford.SplitCl11GradedTensorTower

namespace InfoGeometry.Canonical.GradedChiralSpinMat4CCarrierMap

/-!
# Graded chiral spin tower → `Mat4C` carrier map

This module proves the narrow algebraic carrier map that was missing between the
abstract tower of graded tensor products of real `2 × 2` chiral spin matrices and
the complex `4 × 4` matrix carrier used by the smooth Yang–Mills manifold and the
lattice continuum-limit owners.

The map is `SplitClPower 2 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ` followed by entrywise
`ℝ → ℂ`. It is an injective real-algebra hom with a concrete non-commutativity
witness. It does **not** identify the smooth differential-form geometry or the
analytic `a → 0` limit with the tower; that remains explicit BUCKET 3 debt.

## Three-bucket audit map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `splitClPowerTwoToMat4C`
* `splitClPowerTwoToMat4C_injective`
* `mat4E01_mul_ne`
* `splitClPowerTwoToMat4C_noncomm`
* `exists_noncomm_mat4C`

#### BUCKET 2: CONDITIONAL THEOREMS
* none

#### BUCKET 3: OPEN CLOSURE DEBT
* Smooth `Mat4CForm` Yang–Mills geometry and the lattice `a → 0` Wilson
  limits are not identified with this graded tower; only the finite real
  algebra carrier is transported here.
-/

/-- Complex `4 × 4` matrix carrier. -/
abbrev Mat4C := Matrix (Fin 4) (Fin 4) ℂ

/-- Real `4 × 4` matrix carrier. -/
abbrev Mat4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Real-algebra carrier map from the abstract `n = 2` graded tensor tower to
`Mat4C`, through `splitClPowerEquivMat 2` and entrywise complexification. -/
def splitClPowerTwoToMat4C : SplitClPower 2 →ₐ[ℝ] Mat4C :=
  (Algebra.ofId ℝ ℂ).mapMatrix.comp (splitClPowerEquivMat 2).toAlgHom

/-- The map acts as entrywise complexification of the real matrix realization. -/
theorem splitClPowerTwoToMat4C_apply (a : SplitClPower 2) :
    splitClPowerTwoToMat4C a = (splitClPowerEquivMat 2 a).map (Algebra.ofId ℝ ℂ) :=
  rfl

/-- Entrywise form of the carrier map. -/
theorem splitClPowerTwoToMat4C_apply_entry (a : SplitClPower 2) (i j : Fin 4) :
    splitClPowerTwoToMat4C a i j = (splitClPowerEquivMat 2 a i j : ℂ) :=
  rfl

/-- The carrier map is injective, hence the graded tower is faithfully represented. -/
theorem splitClPowerTwoToMat4C_injective : Function.Injective splitClPowerTwoToMat4C := by
  intro a b h
  apply (splitClPowerEquivMat 2).injective
  ext i j
  have hij := congrFun (congrFun h i) j
  change ((splitClPowerEquivMat 2 a) i j : ℂ) =
    ((splitClPowerEquivMat 2 b) i j : ℂ) at hij
  exact Complex.ofReal_injective hij

/-- Elementary upper-triangular real `4 × 4` matrix. -/
def mat4E01 : Mat4R := Matrix.single 0 1 1

/-- Elementary lower-triangular real `4 × 4` matrix. -/
def mat4E10 : Mat4R := Matrix.single 1 0 1

/-- The two elementary matrices do not commute. -/
theorem mat4E01_mul_ne : mat4E01 * mat4E10 ≠ mat4E10 * mat4E01 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [mat4E01, mat4E10, Matrix.mul_apply, Fin.sum_univ_four] at h00

/-- Tower lifts of the elementary matrices. -/
def splitE01 : SplitClPower 2 := (splitClPowerEquivMat 2).symm mat4E01

/-- Tower lifts of the elementary matrices. -/
def splitE10 : SplitClPower 2 := (splitClPowerEquivMat 2).symm mat4E10

/-- Non-commutativity is preserved by the complexified carrier map. -/
theorem splitClPowerTwoToMat4C_noncomm :
    splitClPowerTwoToMat4C splitE01 * splitClPowerTwoToMat4C splitE10 ≠
      splitClPowerTwoToMat4C splitE10 * splitClPowerTwoToMat4C splitE01 := by
  intro h
  apply mat4E01_mul_ne
  ext i j
  have hij := congrFun (congrFun h i) j
  apply Complex.ofReal_injective
  simpa [splitClPowerTwoToMat4C_apply, splitE01, splitE10,
    Matrix.mul_apply, Fin.sum_univ_four] using hij

/-- Complexified elementary matrices in `Mat4C`. -/
def mat4CE01 : Mat4C := mat4E01.map (Algebra.ofId ℝ ℂ)

/-- Complexified elementary matrices in `Mat4C`. -/
def mat4CE10 : Mat4C := mat4E10.map (Algebra.ofId ℝ ℂ)

/-- The complexified elementary matrices do not commute. -/
theorem mat4CE01_mul_ne : mat4CE01 * mat4CE10 ≠ mat4CE10 * mat4CE01 := by
  intro h
  apply mat4E01_mul_ne
  ext i j
  have hij := congrFun (congrFun h i) j
  apply Complex.ofReal_injective
  simpa [mat4CE01, mat4CE10, Matrix.mul_apply, Fin.sum_univ_four] using hij

/-- Explicit non-commutativity witness on the complex `4 × 4` carrier. -/
theorem exists_noncomm_mat4C : ∃ A B : Mat4C, A * B ≠ B * A := by
  exact ⟨mat4CE01, mat4CE10, mat4CE01_mul_ne⟩

end InfoGeometry.Canonical.GradedChiralSpinMat4CCarrierMap
