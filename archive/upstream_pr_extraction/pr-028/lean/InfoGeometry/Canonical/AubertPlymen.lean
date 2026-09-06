import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-!
# Aubert--Plymen twisted group algebra: concrete 2×2 representation

This file is the Lean 4 translation of the SymPy certificate in
`sympy_twisted_algebra.py` for the real matrix slice of the Aubert--Plymen
simple modules.

Paper relation surface:
* `s² = 1`
* `sX = X⁻¹s`, represented here as `s * X z = X z⁻¹ * s`
* `sY = -Ys`
* `XY = YX`

The matrices are:
* `s = [[0,1],[1,0]]`
* `X z = [[z,0],[0,z⁻¹]]`
* `Y w = [[w,0],[0,-w]]`

No axioms. No sorries. No vacuous `True` closure claims.
-/

noncomputable section

namespace AubertPlymen

open scoped Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The Aubert--Plymen involution generator. -/
def s : Mat2 := !![(0 : ℝ), 1; 1, (0 : ℝ)]

/-- The `X` generator on the two-dimensional module `M_{w,z}`. -/
def X (z : ℝ) : Mat2 := !![z, 0; 0, z⁻¹]

/-- The `Y` generator on the two-dimensional module `M_{w,z}`. -/
def Y (w : ℝ) : Mat2 := !![w, 0; 0, -w]

/-- Cl(1,1) positive generator / `Y 1` diagonal atom. -/
def ePlus : Mat2 := Y 1

/-- Cl(1,1) negative generator obtained from the Aubert--Plymen phase flip. -/
def eMinus : Mat2 := s * ePlus

/-- `s² = 1`. -/
theorem s_sq : s * s = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s, Matrix.mul_apply, Fin.sum_univ_two]

/-- `sX = X⁻¹s`, with `X⁻¹` represented by the parameter transform `z ↦ z⁻¹`. -/
theorem sX_eq_Xinv_s (z : ℝ) : s * X z = X z⁻¹ * s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s, X, Matrix.mul_apply, Fin.sum_univ_two]

/-- The cocycle anticommutation relation `sY = -Ys`. -/
theorem sY_eq_neg_Ys (w : ℝ) : s * Y w = -Y w * s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s, Y, Matrix.mul_apply, Fin.sum_univ_two]

/-- The commuting relation `XY = YX`. -/
theorem XY_eq_YX (z w : ℝ) : X z * Y w = Y w * X z := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Conjugation by `s` sends `X z` to `X z⁻¹`; since `s⁻¹ = s`, this is `sXs`. -/
theorem sXs_eq_Xinv (z : ℝ) : s * X z * s = X z⁻¹ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s, X, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by `s` sends `Y w` to `Y (-w)`. -/
theorem sYs_eq_Yneg (w : ℝ) : s * Y w * s = Y (-w) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s, Y, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `Y 1` diagonal atom squares to `1`. -/
theorem ePlus_sq : ePlus * ePlus = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [ePlus, Y, Matrix.mul_apply, Fin.sum_univ_two]

/-- The phase-flipped off-diagonal atom squares to `-1`. -/
theorem eMinus_sq : eMinus * eMinus = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [eMinus, ePlus, s, Y, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two Cl(1,1) atoms anticommute. -/
theorem ePlus_eMinus_anticomm : ePlus * eMinus + eMinus * ePlus = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [eMinus, ePlus, s, Y, Matrix.mul_apply, Fin.sum_univ_two]

/-- One-dimensional scalar realizations are incompatible with nonzero `s` and nonzero `Y`. -/
theorem no_one_dimensional_scalar_model {sigma y : ℝ}
    (hsigma : sigma ≠ 0) (hy : y ≠ 0) (h : sigma * y = -(y * sigma)) : False := by
  have hzero : sigma * y = 0 := by
    nlinarith [h]
  exact (mul_ne_zero hsigma hy) hzero

/-- Kernel-checked package of the concrete Aubert--Plymen relation surface. -/
theorem relation_package (z w : ℝ) :
    s * s = 1 ∧
    s * X z = X z⁻¹ * s ∧
    s * Y w = -Y w * s ∧
    X z * Y w = Y w * X z ∧
    s * X z * s = X z⁻¹ ∧
    s * Y w * s = Y (-w) := by
  exact ⟨s_sq, sX_eq_Xinv_s z, sY_eq_neg_Ys w, XY_eq_YX z w,
    sXs_eq_Xinv z, sYs_eq_Yneg w⟩

end AubertPlymen

end
