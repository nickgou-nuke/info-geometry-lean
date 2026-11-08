/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SpinAffineCasimirRigidity
import Mathlib.Algebra.Star.Unitary

/-! # Explicit unitary realization of the permitted fixed-Cartan phases

The rigidity owner classifies the admissible coefficients. Here the resulting
phase rotation is realized on its original spin matrices by `diag(u, 1)`.
-/

noncomputable section
namespace InfoGeometry.Physics.SpinAffineCasimirRigidity

open InfoGeometry.Physics.NuclearWignerSupermultiplet

/-- A phase on the positive spin basis vector and identity on the negative one. -/
def phaseMatrix (u : ℂ) : SpinMatrix := !![u, 0; 0, 1]

/-- Unit-modulus coefficients give an actual unitary matrix. -/
theorem phaseMatrix_mem_unitary (u : ℂ) (hu : Complex.normSq u = 1) :
    phaseMatrix u ∈ unitary SpinMatrix := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      ← Complex.normSq_eq_conj_mul_self, Complex.mul_conj, hu]

/-- The raising operator acquires precisely the allowed phase. -/
theorem phaseMatrix_conjugate_plus (u : ℂ) :
    phaseMatrix u * isospinPlus * star (phaseMatrix u) = mixedPlus u 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, mixedPlus, isospinPlus, isospinMinus, pauli1, pauli2,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

/-- The lowering operator acquires the conjugate phase required by the owner. -/
theorem phaseMatrix_conjugate_minus (u : ℂ) :
    phaseMatrix u * isospinMinus * star (phaseMatrix u) = mixedMinus u 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, mixedMinus, isospinPlus, isospinMinus, pauli1, pauli2,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  ring

/-- For unit-modulus coefficients the fixed Cartan is unchanged. -/
theorem phaseMatrix_conjugate_cartan (u : ℂ) (hu : Complex.normSq u = 1) :
    phaseMatrix u * isospin3 * star (phaseMatrix u) = isospin3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, isospin3, pauli3, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply]
  · calc u * (2 : ℂ)⁻¹ * starRingEnd ℂ u = (2 : ℂ)⁻¹ * (u * starRingEnd ℂ u) := by ring
      _ = (2 : ℂ)⁻¹ := by rw [Complex.mul_conj, hu]; norm_num

end InfoGeometry.Physics.SpinAffineCasimirRigidity
