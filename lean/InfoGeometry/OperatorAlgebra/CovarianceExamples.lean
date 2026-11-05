/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CovarianceKraus

/-!
# Noncommuting covariance examples

These full complex matrices witness order-sensitive transport, a non-Hermitian
directed lag, and finite stabilization with noncommuting positive noise. They
exercise the arbitrary-dimension theorems; they do not restrict their carriers.
-/

namespace InfoGeometry.OperatorAlgebra.CovarianceExamples

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.CovarianceTransport
open InfoGeometry.OperatorAlgebra.CovarianceDynamics
open InfoGeometry.Canonical.FiniteSteinInverse

def upperShear : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
def lowerShear : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 1]
def shift : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Full positive innovation covariance, given by its Gram factor. -/
def noise : Matrix (Fin 2) (Fin 2) ℂ := upperShear * upperShearᴴ

theorem noise_posSemidef : noise.PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose upperShear

theorem noise_entries : noise = !![2, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [noise, upperShear, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

/-- A closed noncommutativity witness on the actual complex matrix carrier. -/
theorem shears_do_not_commute : upperShear * lowerShear ≠ lowerShear * upperShear := by
  intro h
  have h₀₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  norm_num [upperShear, lowerShear, Matrix.mul_apply, Fin.sum_univ_two] at h₀₀

/-- Here exchanging the two factors changes the full covariance update. -/
theorem gain_mixing_changes_covariance :
    covarianceStep (lowerShear * upperShear) noise noise ≠
      covarianceStep (upperShear * lowerShear) noise noise := by
  intro h
  have h₀₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  norm_num [covarianceStep, noise_entries, upperShear, lowerShear,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_ofNat] at h₀₀

theorem shift_sq : shift ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, shift, Matrix.mul_apply, Fin.sum_univ_two]

/-- Nilpotence does not require the innovation covariance to commute. -/
theorem shift_noise_do_not_commute : shift * noise ≠ noise * shift := by
  intro h
  have h₀₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
  norm_num [shift, noise_entries, Matrix.mul_apply, Fin.sum_univ_two] at h₀₁

/-- The lag of a positive covariance may fail to be Hermitian. -/
theorem lag_not_hermitian : ¬ (shift * noise).IsHermitian := by
  intro h
  have h₀₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h.eq
  norm_num [shift, noise_entries, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply] at h₀₁

theorem stationary_entries :
    finiteStein shift (star shift) noise 2 = !![3, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [finiteStein, Finset.sum_range_succ, shift, noise_entries,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_ofNat]

/-- A constructed full positive stationary covariance, unique without commutation. -/
theorem stationary_unique :
    ∃! C : Matrix (Fin 2) (Fin 2) ℂ,
      C.PosSemidef ∧ covarianceStep shift noise C = C :=
  existsUnique_stationary_covariance shift noise_posSemidef 2 shift_sq

/-- Every initial operator reaches the same full matrix after two updates. -/
theorem stabilization_after_two (C : Matrix (Fin 2) (Fin 2) ℂ) :
    (covarianceStep shift noise)^[2] C = !![3, 1; 1, 1] := by
  rw [covariance_iterate_eq_finiteStein_of_nilpotent shift noise C 2 shift_sq,
    stationary_entries]

end InfoGeometry.OperatorAlgebra.CovarianceExamples
