import Mathlib.Tactic

/-!
# Finite parafermion-style Artin braid matrices

This module records the finite `3 x 3` matrix identity behind the
parafermion-braiding interpretation.

It does not prove a physical `SU(2) -> SU(3)` breaking theorem, Lorentz
covariance, a parafermion quantum field theory, or color confinement.  It proves
only the Artin braid relation for two explicit Burau-style matrices.

#### BUCKET 1: CLOSED FINITE THEOREMS

`su3_parafermion_braiding`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Physical parafermions, Lorentz symmetry, `SU(2)`/`SU(3)` representation theory,
and braid statistics for a Hilbert-space model remain outside this finite
matrix file.
-/

noncomputable section

namespace InfoGeometry.Topology.Parafermion

open Matrix

/-- The `3 x 3` projective carrier used by the finite braid matrices. -/
abbrev ProjMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The unreduced Burau-style first Artin braid generator `σ₁`. -/
def sigma_1 (t : ℂ) : ProjMatrix :=
  ![![1 - t, t, 0],
    ![1,     0, 0],
    ![0,     0, 1]]

/-- The unreduced Burau-style second Artin braid generator `σ₂`. -/
def sigma_2 (t : ℂ) : ProjMatrix :=
  ![![1, 0,     0],
    ![0, 1 - t, t],
    ![0, 1,     0]]

/-- The two unreduced Burau generators have determinant `-t`. -/
theorem sigma_1_det (t : ℂ) : (sigma_1 t).det = -t := by
  simp [sigma_1, Matrix.det_fin_three]

theorem sigma_2_det (t : ℂ) : (sigma_2 t).det = -t := by
  simp [sigma_2, Matrix.det_fin_three]

/-- Away from `t = 0`, each finite braid generator is invertible. -/
theorem sigma_1_isUnit (t : ℂ) (ht : t ≠ 0) : IsUnit (sigma_1 t) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [sigma_1_det]
  exact (isUnit_iff_ne_zero.mpr ht).neg

theorem sigma_2_isUnit (t : ℂ) (ht : t ≠ 0) : IsUnit (sigma_2 t) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [sigma_2_det]
  exact (isUnit_iff_ne_zero.mpr ht).neg

/-- Explicit inverse of the first finite braid generator away from `t = 0`. -/
def sigma_1_inv (t : ℂ) : ProjMatrix :=
  ![![0, 1, 0],
    ![t⁻¹, 1 - t⁻¹, 0],
    ![0, 0, 1]]

/-- Explicit inverse of the second finite braid generator away from `t = 0`. -/
def sigma_2_inv (t : ℂ) : ProjMatrix :=
  ![![1, 0, 0],
    ![0, 0, 1],
    ![0, t⁻¹, 1 - t⁻¹]]

theorem sigma_1_mul_inv (t : ℂ) (ht : t ≠ 0) :
    sigma_1 t * sigma_1_inv t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_1, sigma_1_inv, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [ht] <;> ring

theorem sigma_1_inv_mul (t : ℂ) (ht : t ≠ 0) :
    sigma_1_inv t * sigma_1 t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_1, sigma_1_inv, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [ht] <;> ring

theorem sigma_2_mul_inv (t : ℂ) (ht : t ≠ 0) :
    sigma_2 t * sigma_2_inv t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_2, sigma_2_inv, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [ht] <;> ring

theorem sigma_2_inv_mul (t : ℂ) (ht : t ≠ 0) :
    sigma_2_inv t * sigma_2 t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_2, sigma_2_inv, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [ht] <;> ring

/--
Finite Artin braid relation.

For the explicit matrices above, `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`.
-/
theorem su3_parafermion_braiding (t : ℂ) :
    sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_1, sigma_2, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf

end InfoGeometry.Topology.Parafermion

end noncomputable section
