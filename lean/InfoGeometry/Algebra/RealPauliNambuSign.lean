/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeZornNambuAssociator
import InfoGeometry.Clifford.GullDoranPseudoscalarBridge
import Mathlib.Analysis.Real.Sqrt

/-!
# Real Pauli Nambu equations with an explicit sign convention

The carrier is the existing real `4 × 4` Pauli family. Its real skew phase
`realPhaseAxis` commutes with the three symmetric Pauli generators. The
ternary expression is the existing associative alternating cubic `nambu`.

For real coefficients and a common nonzero spatial scale, the first three
Sochichiu equations force a scalar fourth generator. The Euclidean fourth
equation then forces a negative real fourth power and is impossible.
Changing that fourth equation's sign admits an explicit symmetric solution.
These are finite matrix equations for this common-scale real ansatz; no
classification of arbitrary representations or complex-coefficient ansatz
is asserted. The phase-twisted equations are not a claim that the raw cubic
closes on the real span of the four generators.
-/

noncomputable section

namespace InfoGeometry.Algebra.RealPauliNambuSign

open Matrix
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open InfoGeometry.Algebra.NoncommutativeZornNambu

/-! ## Existing real Pauli family and its transpose/phase laws -/

theorem realSigma1_transpose : realSigma1ᵀ = realSigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realSigma1]

theorem realSigma2_transpose : realSigma2ᵀ = realSigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realSigma2]

theorem realSigma3_transpose : realSigma3ᵀ = realSigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realSigma3]

theorem realPhaseAxis_transpose : realPhaseAxisᵀ = -realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realPhaseAxis]

theorem realPhaseAxis_commutes_sigma1 :
    realPhaseAxis * realSigma1 = realSigma1 * realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, Matrix.mul_apply, Fin.sum_univ_four]

theorem realPhaseAxis_commutes_sigma2 :
    realPhaseAxis * realSigma2 = realSigma2 * realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma2, Matrix.mul_apply, Fin.sum_univ_four]

theorem realPhaseAxis_commutes_sigma3 :
    realPhaseAxis * realSigma3 = realSigma3 * realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma3, Matrix.mul_apply, Fin.sum_univ_four]

theorem realSigma1_mul_realSigma2 :
    realSigma1 * realSigma2 = realPhaseAxis * realSigma3 := by
  rw [← real_pseudoscalar_eq_phaseAxis, mul_assoc, realSigma3_sq, mul_one]

theorem realSigma2_mul_realSigma3 :
    realSigma2 * realSigma3 = realPhaseAxis * realSigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem realSigma3_mul_realSigma1 :
    realSigma3 * realSigma1 = realPhaseAxis * realSigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

/-! ## Four basis equations and their common-scale versions -/

theorem nambu_pauli_triple :
    nambu ⟨realSigma1, realSigma2, realSigma3⟩ = (6 : ℝ) • realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambu, dot, cross, realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem nambu_identity_pauli12 :
    nambu ⟨(1 : Mat4R), realSigma1, realSigma2⟩ =
      (2 : ℝ) • (realPhaseAxis * realSigma3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambu, dot, cross, realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem nambu_identity_pauli23 :
    nambu ⟨(1 : Mat4R), realSigma2, realSigma3⟩ =
      (2 : ℝ) • (realPhaseAxis * realSigma1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambu, dot, cross, realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem nambu_identity_pauli31 :
    nambu ⟨(1 : Mat4R), realSigma3, realSigma1⟩ =
      (2 : ℝ) • (realPhaseAxis * realSigma2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambu, dot, cross, realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- A scalar component in a spatial argument contributes to the general expansion.
A traceless spatial ansatz removes these terms; general spatial arguments require them. -/
theorem nambu_spatial_scalar_counterexample :
    nambu ⟨realSigma2, (1 : Mat4R), realSigma1⟩ =
      (2 : ℝ) • (realPhaseAxis * realSigma3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambu, dot, cross, realPhaseAxis, realSigma1, realSigma2, realSigma3,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem nambu_spatial_scalar_ne_zero :
    nambu ⟨realSigma2, (1 : Mat4R), realSigma1⟩ ≠ 0 := by
  rw [nambu_spatial_scalar_counterexample]
  intro h
  have h01 := congrArg (fun A : Mat4R => A 0 1) h
  norm_num [realPhaseAxis, realSigma3, Matrix.mul_apply, Fin.sum_univ_four] at h01

theorem nambu_scaled_pauli_triple (c : ℝ) :
    nambu ⟨c • realSigma1, c • realSigma2, c • realSigma3⟩ =
      (6 * c ^ 3) • realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nambu, dot, cross, realPhaseAxis, realSigma1, realSigma2, realSigma3] <;> ring

/-- A real linear combination of the existing identity and Pauli generators.
The coefficients are real; this is the symmetric, rather than arbitrary
complex-matrix, ansatz. -/
def pauliLinear (μ0 μ1 μ2 μ3 : ℝ) : Mat4R :=
  μ0 • (1 : Mat4R) + μ1 • realSigma1 + μ2 • realSigma2 + μ3 • realSigma3

theorem pauliLinear_transpose (μ0 μ1 μ2 μ3 : ℝ) :
    (pauliLinear μ0 μ1 μ2 μ3)ᵀ = pauliLinear μ0 μ1 μ2 μ3 := by
  simp [pauliLinear, Matrix.transpose_add, realSigma1_transpose,
    realSigma2_transpose, realSigma3_transpose]

/-- The four coefficient directions are genuinely independent. -/
theorem pauliLinear_eq_zero_iff (μ0 μ1 μ2 μ3 : ℝ) :
    pauliLinear μ0 μ1 μ2 μ3 = 0 ↔ μ0 = 0 ∧ μ1 = 0 ∧ μ2 = 0 ∧ μ3 = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h22 := congrFun (congrFun h 2) 2
    have h02 := congrFun (congrFun h 0) 2
    have h03 := congrFun (congrFun h 0) 3
    simp [pauliLinear, realSigma1, realSigma2, realSigma3] at h00 h22 h02 h03
    exact ⟨by linarith, h02, h03, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [pauliLinear]

theorem nambu_pauliLinear_12 (μ0 μ1 μ2 μ3 c : ℝ) :
    nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma1, c • realSigma2⟩ =
      c ^ 2 • ((2 * μ0) • (realPhaseAxis * realSigma3) +
        (6 * μ3) • realPhaseAxis) := by
  ext i j
  simp only [nambu, dot, cross, pauliLinear, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, realSigma2, realSigma3] <;> ring

theorem nambu_pauliLinear_23 (μ0 μ1 μ2 μ3 c : ℝ) :
    nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma2, c • realSigma3⟩ =
      c ^ 2 • ((2 * μ0) • (realPhaseAxis * realSigma1) +
        (6 * μ1) • realPhaseAxis) := by
  ext i j
  simp only [nambu, dot, cross, pauliLinear, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, realSigma2, realSigma3] <;> ring

theorem nambu_pauliLinear_31 (μ0 μ1 μ2 μ3 c : ℝ) :
    nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma3, c • realSigma1⟩ =
      c ^ 2 • ((2 * μ0) • (realPhaseAxis * realSigma2) +
        (6 * μ2) • realPhaseAxis) := by
  ext i j
  simp only [nambu, dot, cross, pauliLinear, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, realSigma2, realSigma3] <;> ring

/-! ## The first three equations force the scalar fourth-generator sector -/

theorem pauli_coefficients_of_cyclic_nambu_equations
    (μ0 μ1 μ2 μ3 c : ℝ) (hc : c ≠ 0)
    (h12 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma1, c • realSigma2⟩ =
      -(realPhaseAxis * (c • realSigma3)))
    (h23 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma2, c • realSigma3⟩ =
      -(realPhaseAxis * (c • realSigma1)))
    (h31 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma3, c • realSigma1⟩ =
      -(realPhaseAxis * (c • realSigma2))) :
    μ1 = 0 ∧ μ2 = 0 ∧ μ3 = 0 ∧ 2 * μ0 * c = -1 := by
  rw [nambu_pauliLinear_12] at h12
  rw [nambu_pauliLinear_23] at h23
  rw [nambu_pauliLinear_31] at h31
  have h12a := congrFun (congrFun h12 0) 1
  have h12b := congrFun (congrFun h12 2) 3
  have h23a := congrFun (congrFun h23 0) 1
  have h31a := congrFun (congrFun h31 0) 1
  simp [realPhaseAxis, realSigma1, realSigma2, realSigma3] at h12a h12b h23a h31a
  have hμ1 : μ1 = 0 := h23a.resolve_left hc
  have hμ2 : μ2 = 0 := h31a.resolve_left hc
  have hμ3 : μ3 = 0 := by
    have h : c ^ 2 * μ3 = 0 := by nlinarith [h12a, h12b]
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hc)
  have hscale : 2 * μ0 * c = -1 := by
    have h : c * (2 * μ0 * c + 1) = 0 := by nlinarith [h12a, h12b]
    have hz := (mul_eq_zero.mp h).resolve_left hc
    linarith
  exact ⟨hμ1, hμ2, hμ3, hscale⟩

/-- Exact centralization in the stated real common-scale Pauli ansatz. -/
theorem pauliLinear_eq_scalar_of_cyclic_nambu_equations
    (μ0 μ1 μ2 μ3 c : ℝ) (hc : c ≠ 0)
    (h12 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma1, c • realSigma2⟩ =
      -(realPhaseAxis * (c • realSigma3)))
    (h23 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma2, c • realSigma3⟩ =
      -(realPhaseAxis * (c • realSigma1)))
    (h31 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma3, c • realSigma1⟩ =
      -(realPhaseAxis * (c • realSigma2))) :
    pauliLinear μ0 μ1 μ2 μ3 = μ0 • (1 : Mat4R) ∧ 2 * μ0 * c = -1 := by
  obtain ⟨h1, h2, h3, hscale⟩ :=
    pauli_coefficients_of_cyclic_nambu_equations μ0 μ1 μ2 μ3 c hc h12 h23 h31
  exact ⟨by simp [pauliLinear, h1, h2, h3], hscale⟩

/-- The Euclidean fourth equation forces the spin-half negative fourth power.
This is a conditional algebraic reduction used by the following impossibility
theorem; the displayed real hypotheses have no simultaneous solution. -/
theorem euclidean_pauli_equations_force_negative_quartic
    (μ0 μ1 μ2 μ3 c : ℝ) (hc : c ≠ 0)
    (h12 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma1, c • realSigma2⟩ =
      -(realPhaseAxis * (c • realSigma3)))
    (h23 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma2, c • realSigma3⟩ =
      -(realPhaseAxis * (c • realSigma1)))
    (h31 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma3, c • realSigma1⟩ =
      -(realPhaseAxis * (c • realSigma2)))
    (h123 : nambu ⟨c • realSigma1, c • realSigma2, c • realSigma3⟩ =
      realPhaseAxis * pauliLinear μ0 μ1 μ2 μ3) :
    μ0 ^ 4 = -(3 / 4 : ℝ) := by
  obtain ⟨hscalar, hscale⟩ :=
    pauliLinear_eq_scalar_of_cyclic_nambu_equations μ0 μ1 μ2 μ3 c hc h12 h23 h31
  rw [nambu_scaled_pauli_triple, hscalar] at h123
  have h123a := congrFun (congrFun h123 0) 1
  simp [realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four] at h123a
  have hcube : (2 * μ0 * c) ^ 3 = (-1 : ℝ) ^ 3 := congrArg (fun x : ℝ => x ^ 3) hscale
  have hprod : μ0 ^ 3 * (6 * c ^ 3) = μ0 ^ 4 := by
    have hcubic : 6 * c ^ 3 = μ0 := by linarith [h123a]
    rw [hcubic]
    ring
  nlinarith [hcube, hprod]

theorem no_real_common_scale_euclidean_pauli_solution
    (μ0 μ1 μ2 μ3 c : ℝ) (hc : c ≠ 0)
    (h12 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma1, c • realSigma2⟩ =
      -(realPhaseAxis * (c • realSigma3)))
    (h23 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma2, c • realSigma3⟩ =
      -(realPhaseAxis * (c • realSigma1)))
    (h31 : nambu ⟨pauliLinear μ0 μ1 μ2 μ3, c • realSigma3, c • realSigma1⟩ =
      -(realPhaseAxis * (c • realSigma2)))
    (h123 : nambu ⟨c • realSigma1, c • realSigma2, c • realSigma3⟩ =
      realPhaseAxis * pauliLinear μ0 μ1 μ2 μ3) : False := by
  have hquartic := euclidean_pauli_equations_force_negative_quartic
    μ0 μ1 μ2 μ3 c hc h12 h23 h31 h123
  nlinarith [sq_nonneg (μ0 ^ 2)]

/-! ## Explicit symmetric solution when the fourth equation changes sign -/

/-- The positive real fourth root of `3/4`, expressed with native square roots. -/
def symmetricScale : ℝ := Real.sqrt (Real.sqrt (3 / 4 : ℝ))

def symmetricSpatialScale : ℝ := -(2 * symmetricScale)⁻¹

theorem symmetricScale_pos : 0 < symmetricScale := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3 / 4))

theorem symmetricScale_ne_zero : symmetricScale ≠ 0 := ne_of_gt symmetricScale_pos

theorem symmetricScale_fourth : symmetricScale ^ 4 = (3 / 4 : ℝ) := by
  unfold symmetricScale
  calc
    Real.sqrt (Real.sqrt (3 / 4 : ℝ)) ^ 4 =
        (Real.sqrt (Real.sqrt (3 / 4 : ℝ)) ^ 2) ^ 2 := by ring
    _ = Real.sqrt (3 / 4 : ℝ) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
    _ = 3 / 4 := Real.sq_sqrt (by norm_num)

theorem symmetricSpatialScale_ne_zero : symmetricSpatialScale ≠ 0 := by
  simp [symmetricSpatialScale, symmetricScale_ne_zero]

theorem symmetric_scales_relation : 2 * symmetricScale * symmetricSpatialScale = -1 := by
  unfold symmetricSpatialScale
  field_simp [symmetricScale_ne_zero]

theorem symmetric_spatial_cube : 6 * symmetricSpatialScale ^ 3 = -symmetricScale := by
  unfold symmetricSpatialScale
  field_simp [symmetricScale_ne_zero]
  nlinarith [symmetricScale_fourth]

def symmetricT1 : Mat4R := symmetricSpatialScale • realSigma1
def symmetricT2 : Mat4R := symmetricSpatialScale • realSigma2
def symmetricT3 : Mat4R := symmetricSpatialScale • realSigma3
def symmetricT4 : Mat4R := symmetricScale • (1 : Mat4R)

theorem symmetricT1_transpose : symmetricT1ᵀ = symmetricT1 := by
  simp [symmetricT1, realSigma1_transpose]

theorem symmetricT2_transpose : symmetricT2ᵀ = symmetricT2 := by
  simp [symmetricT2, realSigma2_transpose]

theorem symmetricT3_transpose : symmetricT3ᵀ = symmetricT3 := by
  simp [symmetricT3, realSigma3_transpose]

theorem symmetricT4_transpose : symmetricT4ᵀ = symmetricT4 := by
  simp [symmetricT4]

theorem symmetricT1_ne_zero : symmetricT1 ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  exact symmetricSpatialScale_ne_zero (by simpa [symmetricT1, realSigma1] using h02)

theorem symmetricT2_ne_zero : symmetricT2 ≠ 0 := by
  intro h
  have h03 := congrFun (congrFun h 0) 3
  exact symmetricSpatialScale_ne_zero (by simpa [symmetricT2, realSigma2] using h03)

theorem symmetricT3_ne_zero : symmetricT3 ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  exact symmetricSpatialScale_ne_zero (by simpa [symmetricT3, realSigma3] using h00)

theorem symmetricT4_ne_zero : symmetricT4 ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  exact symmetricScale_ne_zero (by simpa [symmetricT4] using h00)

private theorem symmetric_scales_quadratic :
    2 * symmetricScale * symmetricSpatialScale ^ 2 = -symmetricSpatialScale := by
  have h := congrArg (fun x : ℝ => x * symmetricSpatialScale) symmetric_scales_relation
  nlinarith [h]

theorem symmetric_nambu_412 :
    nambu ⟨symmetricT4, symmetricT1, symmetricT2⟩ =
      -(realPhaseAxis * symmetricT3) := by
  have h := nambu_pauliLinear_12 symmetricScale 0 0 0 symmetricSpatialScale
  simp only [pauliLinear, zero_smul, add_zero] at h
  rw [show symmetricT4 = symmetricScale • (1 : Mat4R) from rfl,
    show symmetricT1 = symmetricSpatialScale • realSigma1 from rfl,
    show symmetricT2 = symmetricSpatialScale • realSigma2 from rfl, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricT3, realPhaseAxis, realSigma3] <;>
      nlinarith [symmetric_scales_quadratic]

theorem symmetric_nambu_423 :
    nambu ⟨symmetricT4, symmetricT2, symmetricT3⟩ =
      -(realPhaseAxis * symmetricT1) := by
  have h := nambu_pauliLinear_23 symmetricScale 0 0 0 symmetricSpatialScale
  simp only [pauliLinear, zero_smul, add_zero] at h
  rw [show symmetricT4 = symmetricScale • (1 : Mat4R) from rfl,
    show symmetricT2 = symmetricSpatialScale • realSigma2 from rfl,
    show symmetricT3 = symmetricSpatialScale • realSigma3 from rfl, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricT1, realPhaseAxis, realSigma1] <;>
      nlinarith [symmetric_scales_quadratic]

theorem symmetric_nambu_431 :
    nambu ⟨symmetricT4, symmetricT3, symmetricT1⟩ =
      -(realPhaseAxis * symmetricT2) := by
  have h := nambu_pauliLinear_31 symmetricScale 0 0 0 symmetricSpatialScale
  simp only [pauliLinear, zero_smul, add_zero] at h
  rw [show symmetricT4 = symmetricScale • (1 : Mat4R) from rfl,
    show symmetricT3 = symmetricSpatialScale • realSigma3 from rfl,
    show symmetricT1 = symmetricSpatialScale • realSigma1 from rfl, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricT2, realPhaseAxis, realSigma2] <;>
      nlinarith [symmetric_scales_quadratic]

theorem symmetric_nambu_123 :
    nambu ⟨symmetricT1, symmetricT2, symmetricT3⟩ =
      -(realPhaseAxis * symmetricT4) := by
  rw [symmetricT1, symmetricT2, symmetricT3, nambu_scaled_pauli_triple,
    symmetric_spatial_cube]
  simp [symmetricT4]

/-- Four actual symmetric real matrices satisfy all four displayed sign-flipped
equations. This packet does not infer a general Hermitian representation
classification or a raw-cubic real-span closure theorem. -/
theorem symmetric_sign_flipped_nambu_solution :
    symmetricT1ᵀ = symmetricT1 ∧ symmetricT2ᵀ = symmetricT2 ∧
    symmetricT3ᵀ = symmetricT3 ∧ symmetricT4ᵀ = symmetricT4 ∧
    nambu ⟨symmetricT4, symmetricT1, symmetricT2⟩ = -(realPhaseAxis * symmetricT3) ∧
    nambu ⟨symmetricT4, symmetricT2, symmetricT3⟩ = -(realPhaseAxis * symmetricT1) ∧
    nambu ⟨symmetricT4, symmetricT3, symmetricT1⟩ = -(realPhaseAxis * symmetricT2) ∧
    nambu ⟨symmetricT1, symmetricT2, symmetricT3⟩ = -(realPhaseAxis * symmetricT4) :=
  ⟨symmetricT1_transpose, symmetricT2_transpose, symmetricT3_transpose,
    symmetricT4_transpose, symmetric_nambu_412, symmetric_nambu_423,
    symmetric_nambu_431, symmetric_nambu_123⟩

end InfoGeometry.Algebra.RealPauliNambuSign
