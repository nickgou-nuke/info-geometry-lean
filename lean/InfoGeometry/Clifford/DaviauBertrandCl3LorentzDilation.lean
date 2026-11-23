/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic
import InfoGeometry.Clifford.QuaternionPauliRealForm
import InfoGeometry.Clifford.DaviauRealDirac8x8
import InfoGeometry.Clifford.DaviauChiralPeirceSU2
import InfoGeometry.Clifford.LochakRodichevFierzKrein

/-!
# Daviau & Bertrand (2018): Real 8D `Cl₃ ≅ M₂(ℂ)` and `GL(2,ℂ) → ℝ₊ × SO⁺(1,3)`

Formalizes the three algebraic pillars of Daviau & Bertrand (2018, pp. 250–258, documented in
`docs/LOCHAK_2007_DAVIAU_2001_DIGEST.md` §4):

1. **Real 8-dimensional isomorphism `CliffordAlgebra q3Real ≃ₐ[ℝ] M₂(ℂ)`**: explicit inverse
   on `{1, σ₁, σ₂, σ₃, iσ₁, iσ₂, iσ₃, iI₂}` and finite-dimensional equality `8 = 8`.
2. **Four square-`-1` units `u(1) ⊕ su(2)` and associative Daviau embedding `M₂(ℂ) →ₐ[ℝ] M₈(ℝ)`**:
   formalizes `dbI1, dbI2, dbI3, dbI` (Eq. 11) and maps them verbatim onto Daviau's
   `(-P₁, -P₂, -P₃, Γ⁰¹²³)` via `e_k ↦ Γ⁰¹²³ P_{k+1}`.
3. **Spinor carrier `Vec8R ≃ₗ[ℝ] M₂(ℂ)` & charge conjugation `φ_p = -φ σ₁` (Eqs. 3–10)**:
   identifies `det(φ) = star ⟨ξ, η⟩`, `2 Re(det φ) = Ω₁`, `2 Im(det φ) = Ω₂`,
   `Tr(φ φᴴ) = J⁰`, and `Tr(φ σ₃ φᴴ) = Σ⁰`.
4. **Lorentz–dilation double cover `GL(2,ℂ) → ℝ₊ × SO⁺(1,3)` (Eqs. 15–33)**:
   for `R(x) = M x Mᴴ`, proves metric dilation `Rᵀ η R = |det M|² η`, positivity
   `2 R⁰₀ = |a|² + |b|² + |c|² + |d|²`, quartic determinant `det R = |det M|⁴` (via change of
   basis on `End_ℂ(M₂(ℂ))`), and restriction to `SL(2,ℂ) → SO⁺(1,3)` with exact `{±I}` kernel.
-/

noncomputable section

open scoped Kronecker Matrix ComplexConjugate
open Matrix Module
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.QuaternionPauliRealForm hiding Mat2C
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.DaviauChiralPeirceSU2
open InfoGeometry.Clifford.LochakRodichevFierzKrein

namespace InfoGeometry.Clifford.DaviauBertrandCl3LorentzDilation

private abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-! ### 1. Real 8D Clifford Algebra `Cl(3, 0) ≃ₐ[ℝ] M₂(ℂ)` -/

/-- Positive-definite Euclidean quadratic form `v₀² + v₁² + v₂²` on `ℝ³`. -/
def q3Real : QuadraticForm ℝ (Fin 3 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 3 => (1 : ℝ))

@[simp]
theorem q3Real_apply (v : Fin 3 → ℝ) :
    q3Real v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [q3Real, Fin.sum_univ_three, sq]

/-- Standard orthonormal Clifford generators `e₁, e₂, e₃` inside `CliffordAlgebra q3Real`. -/
def e1R : CliffordAlgebra q3Real := CliffordAlgebra.ι q3Real ![1, 0, 0]
def e2R : CliffordAlgebra q3Real := CliffordAlgebra.ι q3Real ![0, 1, 0]
def e3R : CliffordAlgebra q3Real := CliffordAlgebra.ι q3Real ![0, 0, 1]

private lemma e1R_sq : e1R * e1R = 1 := by
  rw [e1R, CliffordAlgebra.ι_sq_scalar]
  simp [q3Real_apply, Algebra.algebraMap_eq_smul_one]

private lemma e2R_sq : e2R * e2R = 1 := by
  rw [e2R, CliffordAlgebra.ι_sq_scalar]
  simp [q3Real_apply, Algebra.algebraMap_eq_smul_one]

private lemma e3R_sq : e3R * e3R = 1 := by
  rw [e3R, CliffordAlgebra.ι_sq_scalar]
  simp [q3Real_apply, Algebra.algebraMap_eq_smul_one]

private lemma polar_q3Real (u v : Fin 3 → ℝ) (h : ∑ i : Fin 3, u i * v i = 0) :
    QuadraticMap.polar q3Real u v = 0 := by
  dsimp [QuadraticMap.polar]
  simp only [q3Real_apply, Pi.add_apply]
  rw [Fin.sum_univ_three] at h
  linarith

private lemma e1R_mul_e2R_neg : e1R * e2R = -(e2R * e1R) := by
  rw [e1R, e2R, CliffordAlgebra.ι_mul_ι_comm, polar_q3Real _ _ (by simp [Fin.sum_univ_three]),
    map_zero, zero_sub]

private lemma e1R_mul_e3R_neg : e1R * e3R = -(e3R * e1R) := by
  rw [e1R, e3R, CliffordAlgebra.ι_mul_ι_comm, polar_q3Real _ _ (by simp [Fin.sum_univ_three]),
    map_zero, zero_sub]

private lemma e2R_mul_e3R_neg : e2R * e3R = -(e3R * e2R) := by
  rw [e2R, e3R, CliffordAlgebra.ι_mul_ι_comm, polar_q3Real _ _ (by simp [Fin.sum_univ_three]),
    map_zero, zero_sub]

private lemma e2R_mul_e1R : e2R * e1R = -(e1R * e2R) :=
  (neg_eq_iff_eq_neg.mpr e1R_mul_e2R_neg).symm

private lemma e3R_mul_e2R : e3R * e2R = -(e2R * e3R) :=
  (neg_eq_iff_eq_neg.mpr e2R_mul_e3R_neg).symm

private lemma e3R_mul_e1R : e3R * e1R = -(e1R * e3R) :=
  (neg_eq_iff_eq_neg.mpr e1R_mul_e3R_neg).symm

private def vol3R : CliffordAlgebra q3Real := e1R * (e2R * e3R)

/-- Explicit Trap T16 noncommutativity witness for `Mat2C`. -/
theorem mat2C_mul_noncomm_witness :
    ∃ A B : Mat2C, A * B ≠ B * A := by
  refine ⟨sigma1, sigma2, ?_⟩
  intro h
  have h00 := congrArg (fun M : Mat2C => (M 0 0).im) h
  simp [sigma1, sigma2, Matrix.mul_apply, Fin.sum_univ_two] at h00
  norm_num at h00

/-- Explicit Trap T16 noncommutativity witness for `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem mat4R_mul_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h01
  norm_num at h01

/-- Explicit Trap T16 noncommutativity witness for `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem mat8R_mul_noncomm_witness :
    ∃ A B : Mat8R, A * B ≠ B * A :=
  ⟨gammaR 0, gammaR 1, daviau_mat8_noncomm.1⟩

/-- Real linear Pauli lift `ℝ³ →ₗ[ℝ] M₂(ℂ)` sending `(v₀, v₁, v₂) ↦ v₀ σ₁ + v₁ σ₂ + v₂ σ₃`. -/
def pauliLiftLin : (Fin 3 → ℝ) →ₗ[ℝ] Mat2C where
  toFun v := (v 0 : ℂ) • sigma1 + (v 1 : ℂ) • sigma2 + (v 2 : ℂ) • sigma3
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigma1, sigma2, sigma3] <;> ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigma1, sigma2, sigma3] <;> ring

private theorem pauliLiftLin_sq (v : Fin 3 → ℝ) :
    pauliLiftLin v * pauliLiftLin v = algebraMap ℝ Mat2C (q3Real v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauliLiftLin, q3Real_apply, sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, pow_two] <;>
    ring

/-- Canonical real `ℝ`-algebra homomorphism `CliffordAlgebra q3Real →ₐ[ℝ] M₂(ℂ)`. -/
def cl3RealToMat2C : CliffordAlgebra q3Real →ₐ[ℝ] Mat2C :=
  CliffordAlgebra.lift q3Real ⟨pauliLiftLin, pauliLiftLin_sq⟩

@[simp] private lemma cl3RealToMat2C_e1R : cl3RealToMat2C e1R = sigma1 := by
  rw [e1R, cl3RealToMat2C, CliffordAlgebra.lift_ι_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliLiftLin, sigma1, sigma2, sigma3]

@[simp] private lemma cl3RealToMat2C_e2R : cl3RealToMat2C e2R = sigma2 := by
  rw [e2R, cl3RealToMat2C, CliffordAlgebra.lift_ι_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliLiftLin, sigma1, sigma2, sigma3]

@[simp] private lemma cl3RealToMat2C_e3R : cl3RealToMat2C e3R = sigma3 := by
  rw [e3R, cl3RealToMat2C, CliffordAlgebra.lift_ι_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliLiftLin, sigma1, sigma2, sigma3]

/-- Explicit Trap T16 noncommutativity witness for `CliffordAlgebra q3Real`. -/
theorem cl3Real_mul_noncomm_witness :
    ∃ A B : CliffordAlgebra q3Real, A * B ≠ B * A := by
  refine ⟨e1R, e2R, ?_⟩
  intro h
  have hM := congrArg cl3RealToMat2C h
  simp only [map_mul, cl3RealToMat2C_e1R, cl3RealToMat2C_e2R] at hM
  have h00 := congrArg (fun M : Mat2C => (M 0 0).im) hM
  simp [sigma1, sigma2, Matrix.mul_apply, Fin.sum_univ_two] at h00
  norm_num at h00

private lemma sigma2_mul_sigma3 : sigma2 * sigma3 = Complex.I • sigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

private lemma sigma3_mul_sigma1 : sigma3 * sigma1 = Complex.I • sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

private lemma sigma1_mul_sigma2 : sigma1 * sigma2 = Complex.I • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

private lemma sigma1_mul_sigma2_mul_sigma3 :
    sigma1 * (sigma2 * sigma3) = Complex.I • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

private lemma real_mul_add_div_two (c a b : ℝ) :
    (c * a + c * b) / 2 = c * ((a + b) / 2) := by
  ring

private lemma real_mul_sub_div_two (c a b : ℝ) :
    (c * a - c * b) / 2 = c * ((a - b) / 2) := by
  ring

private lemma real_neg_mul_sub_div_two (c a b : ℝ) :
    -(c * a - c * b) / 2 = c * (-(a - b) / 2) := by
  ring

private lemma real_add_pair_div_two (a₁ a₂ b₁ b₂ : ℝ) :
    ((a₁ + b₁) + (a₂ + b₂)) / 2 = (a₁ + a₂) / 2 + (b₁ + b₂) / 2 := by
  ring

private lemma real_sub_pair_div_two (a₁ a₂ b₁ b₂ : ℝ) :
    ((a₁ + b₁) - (a₂ + b₂)) / 2 = (a₁ - a₂) / 2 + (b₁ - b₂) / 2 := by
  ring

private lemma real_neg_sub_pair_div_two (a₁ a₂ b₁ b₂ : ℝ) :
    -((a₁ + b₁) - (a₂ + b₂)) / 2 = -(a₁ - a₂) / 2 + -(b₁ - b₂) / 2 := by
  ring

/-- Explicit 8-component real linear inverse `M₂(ℂ) →ₗ[ℝ] CliffordAlgebra q3Real`. -/
def mat2CToCl3RealLin : Mat2C →ₗ[ℝ] CliffordAlgebra q3Real where
  toFun M :=
    (((M 0 0 + M 1 1).re / 2) • (1 : CliffordAlgebra q3Real) +
      ((M 0 1 + M 1 0).re / 2) • e1R +
      (-(M 0 1 - M 1 0).im / 2) • e2R +
      ((M 0 0 - M 1 1).re / 2) • e3R) +
    (((M 0 1 + M 1 0).im / 2) • (e2R * e3R) +
      ((M 0 1 - M 1 0).re / 2) • (e3R * e1R) +
      ((M 0 0 - M 1 1).im / 2) • (e1R * e2R) +
      ((M 0 0 + M 1 1).im / 2) • vol3R)
  map_add' A B := by
    simp only [Matrix.add_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      real_add_pair_div_two, real_sub_pair_div_two, real_neg_sub_pair_div_two, add_smul]
    module
  map_smul' c M := by
    simp only [RingHom.id_apply, Matrix.smul_apply, Complex.real_smul, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, smul_add, smul_smul,
      real_mul_add_div_two, real_mul_sub_div_two, real_neg_mul_sub_div_two]

private theorem cl3RealToMat2C_rightInv (M : Mat2C) :
    cl3RealToMat2C (mat2CToCl3RealLin M) = M := by
  simp only [mat2CToCl3RealLin, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul, map_one,
    map_mul, vol3R, cl3RealToMat2C_e1R, cl3RealToMat2C_e2R, cl3RealToMat2C_e3R,
    sigma2_mul_sigma3, sigma3_mul_sigma1, sigma1_mul_sigma2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;>
        simp [sigma1, sigma2, sigma3, Complex.real_smul] <;>
        ring

private def cl3RealBasisWord (i : Fin 8) : CliffordAlgebra q3Real :=
  match i with
  | 0 => 1
  | 1 => e1R
  | 2 => e2R
  | 3 => e3R
  | 4 => e1R * e2R
  | 5 => e2R * e3R
  | 6 => e3R * e1R
  | 7 => vol3R

private abbrev cl3RealSpan : Submodule ℝ (CliffordAlgebra q3Real) :=
  Submodule.span ℝ (Set.range cl3RealBasisWord)

private lemma cl3RealBasisWord_mem (i : Fin 8) : cl3RealBasisWord i ∈ cl3RealSpan :=
  Submodule.subset_span ⟨i, rfl⟩

private lemma e2R_mul_e3R_mul_e1R : e2R * (e3R * e1R) = vol3R := by
  calc
    e2R * (e3R * e1R) = e2R * -(e1R * e3R) := by rw [e3R_mul_e1R]
    _ = -((e2R * e1R) * e3R) := by rw [mul_neg, mul_assoc]
    _ = -(-(e1R * e2R) * e3R) := by rw [e2R_mul_e1R]
    _ = e1R * (e2R * e3R) := by rw [neg_mul, neg_neg, mul_assoc]

private lemma e3R_mul_e1R_mul_e2R : e3R * (e1R * e2R) = vol3R := by
  calc
    e3R * (e1R * e2R) = (e3R * e1R) * e2R := by rw [← mul_assoc]
    _ = -(e1R * e3R) * e2R := by rw [e3R_mul_e1R]
    _ = -(e1R * (e3R * e2R)) := by rw [neg_mul, mul_assoc]
    _ = -(e1R * -(e2R * e3R)) := by rw [e3R_mul_e2R]
    _ = e1R * (e2R * e3R) := by rw [mul_neg, neg_neg]

private lemma e1R_mul_basis_mem (i : Fin 8) : e1R * cl3RealBasisWord i ∈ cl3RealSpan := by
  fin_cases i
  · change e1R * 1 ∈ cl3RealSpan
    rw [mul_one]
    exact cl3RealBasisWord_mem 1
  · change e1R * e1R ∈ cl3RealSpan
    rw [e1R_sq]
    exact cl3RealBasisWord_mem 0
  · exact cl3RealBasisWord_mem 4
  · change e1R * e3R ∈ cl3RealSpan
    rw [e1R_mul_e3R_neg]
    exact cl3RealSpan.neg_mem (cl3RealBasisWord_mem 6)
  · change e1R * (e1R * e2R) ∈ cl3RealSpan
    rw [← mul_assoc, e1R_sq, one_mul]
    exact cl3RealBasisWord_mem 2
  · exact cl3RealBasisWord_mem 7
  · change e1R * (e3R * e1R) ∈ cl3RealSpan
    rw [← mul_assoc, e1R_mul_e3R_neg, neg_mul, mul_assoc, e1R_sq, mul_one]
    exact cl3RealSpan.neg_mem (cl3RealBasisWord_mem 3)
  · change e1R * vol3R ∈ cl3RealSpan
    rw [vol3R, ← mul_assoc, e1R_sq, one_mul]
    exact cl3RealBasisWord_mem 5

private lemma e2R_mul_basis_mem (i : Fin 8) : e2R * cl3RealBasisWord i ∈ cl3RealSpan := by
  fin_cases i
  · change e2R * 1 ∈ cl3RealSpan
    rw [mul_one]
    exact cl3RealBasisWord_mem 2
  · change e2R * e1R ∈ cl3RealSpan
    rw [e2R_mul_e1R]
    exact cl3RealSpan.neg_mem (cl3RealBasisWord_mem 4)
  · change e2R * e2R ∈ cl3RealSpan
    rw [e2R_sq]
    exact cl3RealBasisWord_mem 0
  · exact cl3RealBasisWord_mem 5
  · change e2R * (e1R * e2R) ∈ cl3RealSpan
    rw [← mul_assoc, e2R_mul_e1R, neg_mul, mul_assoc, e2R_sq, mul_one]
    exact cl3RealSpan.neg_mem (cl3RealBasisWord_mem 1)
  · change e2R * (e2R * e3R) ∈ cl3RealSpan
    rw [← mul_assoc, e2R_sq, one_mul]
    exact cl3RealBasisWord_mem 3
  · change e2R * (e3R * e1R) ∈ cl3RealSpan
    rw [e2R_mul_e3R_mul_e1R]
    exact cl3RealBasisWord_mem 7
  · change e2R * vol3R ∈ cl3RealSpan
    rw [vol3R, ← mul_assoc, e2R_mul_e1R, neg_mul, mul_assoc, ← mul_assoc e2R e2R e3R,
      e2R_sq, one_mul, e1R_mul_e3R_neg, neg_neg]
    exact cl3RealBasisWord_mem 6

private lemma e3R_mul_basis_mem (i : Fin 8) : e3R * cl3RealBasisWord i ∈ cl3RealSpan := by
  fin_cases i
  · change e3R * 1 ∈ cl3RealSpan
    rw [mul_one]
    exact cl3RealBasisWord_mem 3
  · exact cl3RealBasisWord_mem 6
  · change e3R * e2R ∈ cl3RealSpan
    rw [e3R_mul_e2R]
    exact cl3RealSpan.neg_mem (cl3RealBasisWord_mem 5)
  · change e3R * e3R ∈ cl3RealSpan
    rw [e3R_sq]
    exact cl3RealBasisWord_mem 0
  · change e3R * (e1R * e2R) ∈ cl3RealSpan
    rw [e3R_mul_e1R_mul_e2R]
    exact cl3RealBasisWord_mem 7
  · change e3R * (e2R * e3R) ∈ cl3RealSpan
    rw [← mul_assoc, e3R_mul_e2R, neg_mul, mul_assoc, e3R_sq, mul_one]
    exact cl3RealSpan.neg_mem (cl3RealBasisWord_mem 2)
  · change e3R * (e3R * e1R) ∈ cl3RealSpan
    rw [← mul_assoc, e3R_sq, one_mul]
    exact cl3RealBasisWord_mem 1
  · change e3R * vol3R ∈ cl3RealSpan
    have h : e3R * vol3R = e1R * e2R := by
      calc
        e3R * vol3R = e3R * ((e1R * e2R) * e3R) := by rw [vol3R, mul_assoc]
        _ = (e3R * (e1R * e2R)) * e3R := by rw [← mul_assoc]
        _ = vol3R * e3R := by rw [e3R_mul_e1R_mul_e2R]
        _ = e1R * (e2R * (e3R * e3R)) := by rw [vol3R, mul_assoc, mul_assoc]
        _ = e1R * e2R := by rw [e3R_sq, mul_one]
    rw [h]
    exact cl3RealBasisWord_mem 4

private lemma cl3RealSpan_mul_basis (k : Fin 3) {x : CliffordAlgebra q3Real}
    (hx : x ∈ cl3RealSpan) :
    (match k with | 0 => e1R | 1 => e2R | 2 => e3R) * x ∈ cl3RealSpan := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩
    fin_cases k
    · exact e1R_mul_basis_mem i
    · exact e2R_mul_basis_mem i
    · exact e3R_mul_basis_mem i
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact cl3RealSpan.add_mem ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact cl3RealSpan.smul_mem c ha

private theorem mem_cl3RealSpan (x : CliffordAlgebra q3Real) : x ∈ cl3RealSpan := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact cl3RealSpan.smul_mem r (cl3RealBasisWord_mem 0)
  | add a b ha hb => exact cl3RealSpan.add_mem ha hb
  | ι_mul x v hx =>
    have hv : CliffordAlgebra.ι q3Real v =
        v 0 • e1R + v 1 • e2R + v 2 • e3R := by
      have hvec : v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
        ext i; fin_cases i <;> simp
      conv_lhs => rw [hvec]
      rw [map_add, map_add, map_smul, map_smul, map_smul]
      rfl
    rw [hv, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    exact cl3RealSpan.add_mem
      (cl3RealSpan.add_mem
        (cl3RealSpan.smul_mem (v 0) (cl3RealSpan_mul_basis 0 hx))
        (cl3RealSpan.smul_mem (v 1) (cl3RealSpan_mul_basis 1 hx)))
      (cl3RealSpan.smul_mem (v 2) (cl3RealSpan_mul_basis 2 hx))

private theorem mat2CToCl3RealLin_leftInv (x : CliffordAlgebra q3Real) :
    mat2CToCl3RealLin (cl3RealToMat2C x) = x := by
  have hx := mem_cl3RealSpan x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩
    fin_cases i <;>
      · simp only [cl3RealBasisWord, map_one, map_mul, cl3RealToMat2C_e1R, cl3RealToMat2C_e2R,
          cl3RealToMat2C_e3R, vol3R, sigma2_mul_sigma3, sigma3_mul_sigma1, sigma1_mul_sigma2,
          mat2CToCl3RealLin, LinearMap.coe_mk, AddHom.coe_mk]
        simp [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

/-- Real 8-dimensional `ℝ`-algebra isomorphism `CliffordAlgebra q3Real ≃ₐ[ℝ] M₂(ℂ)`
(Daviau & Bertrand 2018, p. 256). -/
def cl3RealEquivMat2C : CliffordAlgebra q3Real ≃ₐ[ℝ] Mat2C :=
  AlgEquiv.ofBijective cl3RealToMat2C
    ⟨Function.LeftInverse.injective mat2CToCl3RealLin_leftInv,
      fun M => ⟨mat2CToCl3RealLin M, cl3RealToMat2C_rightInv M⟩⟩

theorem finrank_cl3Real_and_mat2C :
    Module.finrank ℝ (CliffordAlgebra q3Real) = 8 ∧
    Module.finrank ℝ Mat2C = 8 := by
  have hmat : Module.finrank ℝ Mat2C = 8 := by
    have hmul := Module.finrank_mul_finrank ℝ ℂ Mat2C
    have hc : Module.finrank ℂ Mat2C = 4 := by
      simp [Mat2C, Module.finrank_matrix]
    rw [Complex.finrank_real_complex, hc] at hmul
    linarith
  exact ⟨cl3RealEquivMat2C.toLinearEquiv.finrank_eq.trans hmat, hmat⟩

/-! ### 2. Four Square-`-1` Units `u(1) ⊕ su(2)` & Associative Embedding into `M₈(ℝ)` -/

/-- The three `su(2)` bivectors `i₁ = σ₂σ₃`, `i₂ = σ₃σ₁`, `i₃ = σ₁σ₂` and central pseudoscalar
`i = σ₁σ₂σ₃` in `Cl₃ ≅ M₂(ℂ)` (Daviau & Bertrand 2018, Eq. 11, p. 252). -/
def dbI1 : Mat2C := sigma2 * sigma3
def dbI2 : Mat2C := sigma3 * sigma1
def dbI3 : Mat2C := sigma1 * sigma2
def dbI : Mat2C := sigma1 * sigma2 * sigma3

/-- Algebraic verification of Daviau–Bertrand Eq. (11): all four units square to `-I₂`,
`dbI` is central, and `(dbI1, dbI2, dbI3)` satisfy cyclic quaternionic commutation forming
`u(1) ⊕ su(2)`. -/
theorem four_imag_units_u1_su2 :
    (dbI1 * dbI1 = -1) ∧
    (dbI2 * dbI2 = -1) ∧
    (dbI3 * dbI3 = -1) ∧
    (dbI * dbI = -1) ∧
    (dbI * dbI1 = dbI1 * dbI ∧ dbI * dbI2 = dbI2 * dbI ∧ dbI * dbI3 = dbI3 * dbI) ∧
    (dbI1 * dbI2 = -dbI3 ∧ dbI2 * dbI3 = -dbI1 ∧ dbI3 * dbI1 = -dbI2) ∧
    (dbI1 * dbI2 - dbI2 * dbI1 = -(2 : ℂ) • dbI3) ∧
    (dbI2 * dbI3 - dbI3 * dbI2 = -(2 : ℂ) • dbI1) ∧
    (dbI3 * dbI1 - dbI1 * dbI3 = -(2 : ℂ) • dbI2) := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [dbI1, dbI2, dbI3, dbI, sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply] <;> ring_nf

private def p1Sp : SpMat8Z := ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
private def p2Sp : SpMat8Z := ⟨![2, 3, 0, 1, 6, 7, 4, 5], ![-1, -1, 1, 1, 1, 1, -1, -1]⟩
private def p3Sp : SpMat8Z := ⟨![3, 2, 1, 0, 7, 6, 5, 4], ![-1, 1, -1, 1, 1, -1, 1, -1]⟩
private def g0123Sp : SpMat8Z := ⟨![4, 5, 6, 7, 0, 1, 2, 3], ![1, 1, -1, -1, -1, -1, 1, 1]⟩

private theorem p1Sp_toMat : p1Sp.toMat = p1Z := by decide
private theorem p2Sp_toMat : p2Sp.toMat = p2Z := by decide
private theorem p3Sp_toMat : p3Sp.toMat = p3Z := by decide
private theorem g0123Sp_toMat : g0123Sp.toMat = gamma0123Z := by decide

private lemma gamma5Real_eq_sp (j : Fin 3) :
    gamma5Real j = castZ8 (g0123Sp.mul (match j with | 0 => p1Sp | 1 => p2Sp | 2 => p3Sp)).toMat := by
  fin_cases j
  · dsimp [gamma5Real, gamma0123R, quatPR, quatPZ]
    rw [← g0123Sp_toMat, ← p1Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul]
  · dsimp [gamma5Real, gamma0123R, quatPR, quatPZ]
    rw [← g0123Sp_toMat, ← p2Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul]
  · dsimp [gamma5Real, gamma0123R, quatPR, quatPZ]
    rw [← g0123Sp_toMat, ← p3Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul]

private lemma gamma5Real_anticomm_pair {j k : Fin 3} (hjk : j ≠ k) :
    gamma5Real j * gamma5Real k + gamma5Real k * gamma5Real j = 0 := by
  fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl hjk
    | ( rw [gamma5Real_eq_sp, gamma5Real_eq_sp, ← castZ8_mul, ← castZ8_mul, ← castZ8_add,
          ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← castZ8_zero]
        congr 1; decide )

/-- Real linear lift sending `(v₀, v₁, v₂) ↦ ∑ v_k Γ⁰¹²³ P_{k+1}` in `M₈(ℝ)`. -/
def daviauLiftLin : (Fin 3 → ℝ) →ₗ[ℝ] Mat8R where
  toFun v := v 0 • gamma5Real 0 + v 1 • gamma5Real 1 + v 2 • gamma5Real 2
  map_add' u v := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c v := by simp only [RingHom.id_apply, Pi.smul_apply, smul_add, smul_smul]; rfl

private theorem daviauLiftLin_sq (v : Fin 3 → ℝ) :
    daviauLiftLin v * daviauLiftLin v = algebraMap ℝ Mat8R (q3Real v) := by
  dsimp [daviauLiftLin]
  have h00 := gamma5Real_sq 0
  have h11 := gamma5Real_sq 1
  have h22 := gamma5Real_sq 2
  have h01 := gamma5Real_anticomm_pair (by decide : (0 : Fin 3) ≠ 1)
  have h02 := gamma5Real_anticomm_pair (by decide : (0 : Fin 3) ≠ 2)
  have h12 := gamma5Real_anticomm_pair (by decide : (1 : Fin 3) ≠ 2)
  have hprod :
      (v 0 • gamma5Real 0 + v 1 • gamma5Real 1 + v 2 • gamma5Real 2) *
          (v 0 • gamma5Real 0 + v 1 • gamma5Real 1 + v 2 • gamma5Real 2) =
        (v 0 ^ 2) • (gamma5Real 0 * gamma5Real 0) +
        (v 1 ^ 2) • (gamma5Real 1 * gamma5Real 1) +
        (v 2 ^ 2) • (gamma5Real 2 * gamma5Real 2) +
        (v 0 * v 1) • (gamma5Real 0 * gamma5Real 1 + gamma5Real 1 * gamma5Real 0) +
        (v 0 * v 2) • (gamma5Real 0 * gamma5Real 2 + gamma5Real 2 * gamma5Real 0) +
        (v 1 * v 2) • (gamma5Real 1 * gamma5Real 2 + gamma5Real 2 * gamma5Real 1) := by
    simp only [mul_add, add_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add, smul_smul,
      sq]
    module
  rw [hprod, h00, h11, h22, h01, h02, h12, smul_zero, smul_zero, smul_zero, add_zero, add_zero,
    add_zero, q3Real_apply, Algebra.algebraMap_eq_smul_one, add_smul, add_smul]

/-- Associative real algebra homomorphism `Cl CliffordAlgebra q3Real →ₐ[ℝ] M₈(ℝ)` via
`e_k ↦ Γ^{0123} P_{k+1}`. -/
def cl3RealToDaviauMat8 : CliffordAlgebra q3Real →ₐ[ℝ] Mat8R :=
  CliffordAlgebra.lift q3Real ⟨daviauLiftLin, daviauLiftLin_sq⟩

/-- Associative real algebra embedding `M₂(ℂ) →ₐ[ℝ] M₈(ℝ)` transporting Daviau–Bertrand's
`u(1) ⊕ su(2)` units directly into Daviau's `M₈(ℝ)` commutant and pseudoscalar. -/
def cl3Mat2CToDaviauMat8 : Mat2C →ₐ[ℝ] Mat8R :=
  cl3RealToDaviauMat8.comp cl3RealEquivMat2C.symm.toAlgHom

@[simp] private lemma cl3RealToDaviauMat8_e1R : cl3RealToDaviauMat8 e1R = gamma5Real 0 := by
  rw [e1R, cl3RealToDaviauMat8, CliffordAlgebra.lift_ι_apply]
  simp [daviauLiftLin]

@[simp] private lemma cl3RealToDaviauMat8_e2R : cl3RealToDaviauMat8 e2R = gamma5Real 1 := by
  rw [e2R, cl3RealToDaviauMat8, CliffordAlgebra.lift_ι_apply]
  simp [daviauLiftLin]

@[simp] private lemma cl3RealToDaviauMat8_e3R : cl3RealToDaviauMat8 e3R = gamma5Real 2 := by
  rw [e3R, cl3RealToDaviauMat8, CliffordAlgebra.lift_ι_apply]
  simp [daviauLiftLin]

theorem cl3Mat2CToDaviauMat8_units :
    cl3Mat2CToDaviauMat8 dbI1 = -quatPR 0 ∧
    cl3Mat2CToDaviauMat8 dbI2 = -quatPR 1 ∧
    cl3Mat2CToDaviauMat8 dbI3 = -quatPR 2 ∧
    cl3Mat2CToDaviauMat8 dbI = gamma0123R := by
  have hi1 : cl3RealEquivMat2C.symm dbI1 = e2R * e3R := by
    apply cl3RealEquivMat2C.injective
    rw [cl3RealEquivMat2C.apply_symm_apply]
    symm
    change cl3RealToMat2C (e2R * e3R) = dbI1
    rw [map_mul, cl3RealToMat2C_e2R, cl3RealToMat2C_e3R, dbI1]
  have hi2 : cl3RealEquivMat2C.symm dbI2 = e3R * e1R := by
    apply cl3RealEquivMat2C.injective
    rw [cl3RealEquivMat2C.apply_symm_apply]
    symm
    change cl3RealToMat2C (e3R * e1R) = dbI2
    rw [map_mul, cl3RealToMat2C_e3R, cl3RealToMat2C_e1R, dbI2]
  have hi3 : cl3RealEquivMat2C.symm dbI3 = e1R * e2R := by
    apply cl3RealEquivMat2C.injective
    rw [cl3RealEquivMat2C.apply_symm_apply]
    symm
    change cl3RealToMat2C (e1R * e2R) = dbI3
    rw [map_mul, cl3RealToMat2C_e1R, cl3RealToMat2C_e2R, dbI3]
  have hii : cl3RealEquivMat2C.symm dbI = vol3R := by
    apply cl3RealEquivMat2C.injective
    rw [cl3RealEquivMat2C.apply_symm_apply]
    symm
    change cl3RealToMat2C vol3R = dbI
    rw [vol3R, map_mul, map_mul, cl3RealToMat2C_e1R, cl3RealToMat2C_e2R, cl3RealToMat2C_e3R, dbI,
      mul_assoc]
  have hf12 : gamma5Real 1 * gamma5Real 2 = -quatPR 0 := by
    rw [gamma5Real_eq_sp 1, gamma5Real_eq_sp 2]
    dsimp [quatPR, quatPZ]
    rw [← p1Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← castZ8_neg]
    congr 1; decide
  have hf20 : gamma5Real 2 * gamma5Real 0 = -quatPR 1 := by
    rw [gamma5Real_eq_sp 2, gamma5Real_eq_sp 0]
    dsimp [quatPR, quatPZ]
    rw [← p2Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← castZ8_neg]
    congr 1; decide
  have hf01 : gamma5Real 0 * gamma5Real 1 = -quatPR 2 := by
    rw [gamma5Real_eq_sp 0, gamma5Real_eq_sp 1]
    dsimp [quatPR, quatPZ]
    rw [← p3Sp_toMat, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← castZ8_neg]
    congr 1; decide
  have hf012 : gamma5Real 0 * (gamma5Real 1 * gamma5Real 2) = gamma0123R := by
    rw [gamma5Real_eq_sp 0, gamma5Real_eq_sp 1, gamma5Real_eq_sp 2]
    dsimp [gamma0123R]
    rw [← g0123Sp_toMat, ← castZ8_mul, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul]
    congr 1; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cl3RealToDaviauMat8 (cl3RealEquivMat2C.symm dbI1) = -quatPR 0
    rw [hi1, map_mul, cl3RealToDaviauMat8_e2R, cl3RealToDaviauMat8_e3R, hf12]
  · change cl3RealToDaviauMat8 (cl3RealEquivMat2C.symm dbI2) = -quatPR 1
    rw [hi2, map_mul, cl3RealToDaviauMat8_e3R, cl3RealToDaviauMat8_e1R, hf20]
  · change cl3RealToDaviauMat8 (cl3RealEquivMat2C.symm dbI3) = -quatPR 2
    rw [hi3, map_mul, cl3RealToDaviauMat8_e1R, cl3RealToDaviauMat8_e2R, hf01]
  · change cl3RealToDaviauMat8 (cl3RealEquivMat2C.symm dbI) = gamma0123R
    rw [hii, vol3R, map_mul, map_mul, cl3RealToDaviauMat8_e1R, cl3RealToDaviauMat8_e2R,
      cl3RealToDaviauMat8_e3R, hf012]

/-! ### 3. Spinor Carrier `Vec8R ≃ₗ[ℝ] M₂(ℂ)` & Charge Conjugation `φ_p = -φ σ₁` -/

private def vec8ToCl3SpinorFun (Φ : Vec8R) : Mat2C :=
  !![weylXi Φ 0, -star (weylEta Φ 1); weylXi Φ 1, star (weylEta Φ 0)]

private def cl3SpinorToVec8Fun (φ : Mat2C) : Vec8R :=
  let c : ℝ := 1 / Real.sqrt 2
  let u0 : ℂ := c * (φ 0 0 + star (φ 1 1))
  let u1 : ℂ := c * (φ 1 0 - star (φ 0 1))
  let d0 : ℂ := c * (φ 0 0 - star (φ 1 1))
  let d1 : ℂ := c * (φ 1 0 + star (φ 0 1))
  ![u0.re, -u1.im, -u1.re, u0.im, d0.im, d1.re, d1.im, d0.re]

private lemma inv_sqrt2_pow_two : (Real.sqrt 2 : ℝ)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Explicit real linear equivalence `Vec8R ≃ₗ[ℝ] M₂(ℂ)` identifying Daviau's real 8-spinor
with the Daviau–Bertrand `Cl₃`-spinor matrix `φ` (Eqs. 3–10). -/
def vec8ToCl3Spinor : Vec8R ≃ₗ[ℝ] Mat2C where
  toFun := vec8ToCl3SpinorFun
  map_add' Φ Ψ := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [vec8ToCl3SpinorFun, weylXi, weylEta, phiToPsi, mul_add] <;> ring
  map_smul' r Φ := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [vec8ToCl3SpinorFun, weylXi, weylEta, phiToPsi, Complex.real_smul] <;> ring
  invFun := cl3SpinorToVec8Fun
  left_inv Φ := by
    ext i
    fin_cases i <;>
      · simp [cl3SpinorToVec8Fun, vec8ToCl3SpinorFun, weylXi, weylEta, phiToPsi]
        field_simp
        rw [Real.sq_sqrt (by norm_num)]
        ring
  right_inv φ := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      · simp [vec8ToCl3SpinorFun, cl3SpinorToVec8Fun, weylXi, weylEta, phiToPsi]
        field_simp
        rw [Real.sq_sqrt (by norm_num)]
        ring

@[simp]
private theorem vec8ToCl3Spinor_apply (Φ : Vec8R) :
    vec8ToCl3Spinor Φ = vec8ToCl3SpinorFun Φ :=
  rfl

/-- Positron charge conjugation `φ_p = -φ σ₁` (Daviau & Bertrand 2018, p. 256). -/
def chargeConjCl3 (φ : Mat2C) : Mat2C := -(φ * sigma1)

theorem chargeConjCl3_involutive_and_det (φ : Mat2C) :
    chargeConjCl3 (chargeConjCl3 φ) = φ ∧
    (chargeConjCl3 φ).det = -φ.det := by
  have hs1 : sigma1 * sigma1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigma1, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · dsimp [chargeConjCl3]
    rw [neg_mul, neg_neg, mul_assoc, hs1, mul_one]
  · dsimp [chargeConjCl3]
    simp [Matrix.det_fin_two, sigma1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact correspondence between `Cl₃`-spinor invariants of `vec8ToCl3Spinor Φ` and Daviau's /
Lochak's `M₈(ℝ)` bilinear densities `(Ω₁, Ω₂, J⁰, Σ⁰)`, plus `SL(2,ℂ)` invariance of `det φ`. -/
theorem vec8ToCl3Spinor_fierz_and_currents (Φ : Vec8R) :
    ((vec8ToCl3Spinor Φ).det = star (weylCrossInner Φ)) ∧
    (2 * (vec8ToCl3Spinor Φ).det.re = omega1 Φ) ∧
    (2 * (vec8ToCl3Spinor Φ).det.im = omega2 Φ) ∧
    (4 * Complex.normSq (vec8ToCl3Spinor Φ).det = omega1 Φ ^ 2 + omega2 Φ ^ 2) ∧
    ((vec8ToCl3Spinor Φ * (vec8ToCl3Spinor Φ)ᴴ).trace.re = electricCurrentJ Φ 0) ∧
    ((vec8ToCl3Spinor Φ * sigma3 * (vec8ToCl3Spinor Φ)ᴴ).trace.re = axialCurrentSigma Φ 0) ∧
    (∀ M : Matrix.SpecialLinearGroup (Fin 2) ℂ,
      (M.1 * vec8ToCl3Spinor Φ).det = (vec8ToCl3Spinor Φ).det) := by
  have hdet : (vec8ToCl3Spinor Φ).det = star (weylCrossInner Φ) := by
    rw [vec8ToCl3Spinor_apply, Matrix.det_fin_two]
    apply Complex.ext <;>
      simp [vec8ToCl3SpinorFun, weylCrossInner] <;> ring
  have hre : 2 * (vec8ToCl3Spinor Φ).det.re = omega1 Φ := by
    rw [hdet, Complex.star_def, Complex.conj_re, weylCrossInner_re]
    ring
  have him : 2 * (vec8ToCl3Spinor Φ).det.im = omega2 Φ := by
    rw [hdet, Complex.star_def, Complex.conj_im, weylCrossInner_im]
    ring
  have hnsq : 4 * Complex.normSq (vec8ToCl3Spinor Φ).det = omega1 Φ ^ 2 + omega2 Φ ^ 2 := by
    rw [← hre, ← him, Complex.normSq_apply]
    ring
  have hj0 : (vec8ToCl3Spinor Φ * (vec8ToCl3Spinor Φ)ᴴ).trace.re = electricCurrentJ Φ 0 := by
    rw [vec8ToCl3Spinor_apply, electricCurrentJ0_expand]
    simp [vec8ToCl3SpinorFun, weylXi, weylEta, phiToPsi, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have hs0 :
      (vec8ToCl3Spinor Φ * sigma3 * (vec8ToCl3Spinor Φ)ᴴ).trace.re = axialCurrentSigma Φ 0 := by
    rw [vec8ToCl3Spinor_apply, axialCurrentSigma0_expand]
    simp [vec8ToCl3SpinorFun, weylXi, weylEta, phiToPsi, sigma3, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have hsl : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℂ,
      (M.1 * vec8ToCl3Spinor Φ).det = (vec8ToCl3Spinor Φ).det := by
    intro M
    rw [Matrix.det_mul, M.prop, one_mul]
  exact ⟨hdet, hre, him, hnsq, hj0, hs0, hsl⟩

/-! ### 4. Lorentz–Dilation Double Cover `GL(2,ℂ) → ℝ₊ × SO⁺(1,3)` (Eqs. 15–33) -/

/-- Paravector Pauli basis `σ₀ = I₂, σ₁, σ₂, σ₃` of Herm₂(ℂ). -/
def pauli4 : Fin 4 → Mat2C :=
  ![(1 : Mat2C), sigma1, sigma2, sigma3]

/-- Hermitian `2 × 2` paravector matrix `X(x) = x₀ I₂ + x₁ σ₁ + x₂ σ₂ + x₃ σ₃`. -/
def paravectorMat (x : Fin 4 → ℝ) : Mat2C :=
  ∑ μ : Fin 4, (x μ : ℂ) • pauli4 μ

private lemma pauli4_hermitian (μ : Fin 4) : (pauli4 μ)ᴴ = pauli4 μ := by
  fin_cases μ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli4, sigma1, sigma2, sigma3, Matrix.conjTranspose_apply]

theorem paravectorMat_hermitian (x : Fin 4 → ℝ) : (paravectorMat x)ᴴ = paravectorMat x := by
  dsimp [paravectorMat]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, pauli4_hermitian, star_trivial]

@[simp]
theorem paravectorMat_det (x : Fin 4 → ℝ) :
    (paravectorMat x).det = (minkowskiDot x x : ℂ) := by
  dsimp [paravectorMat, minkowskiDot]
  rw [Fin.sum_univ_four, Matrix.det_fin_two]
  apply Complex.ext <;>
    · simp [pauli4, sigma1, sigma2, sigma3]
      ring

/-- Real `4 × 4` Lorentz–dilation matrix `R^μ_ν(M) = ½ Re Tr(σ_μ M σ_ν Mᴴ)` associated to
any `M ∈ M₂(ℂ)` (Daviau & Bertrand 2018, Eqs. 15–22). -/
def lorentzDilationMat (M : Mat2C) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => ((1 / 2 : ℂ) * (pauli4 μ * M * pauli4 ν * Mᴴ).trace).re

/-- Minkowski metric matrix `η = diag(1, -1, -1, -1)`. -/
def minkowskiEta4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

private lemma pauli4_trace_herm_im_zero (H : Mat2C) (hH : Hᴴ = H) (μ : Fin 4) :
    ((1 / 2 : ℂ) * (pauli4 μ * H).trace).im = 0 := by
  have h00 : (H 0 0).im = 0 := by
    have h := congrArg Complex.im (congrFun (congrFun hH 0) 0)
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  have h11 : (H 1 1).im = 0 := by
    have h := congrArg Complex.im (congrFun (congrFun hH 1) 1)
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  have h10re : (H 1 0).re = (H 0 1).re := by
    have h := congrArg Complex.re (congrFun (congrFun hH 0) 1)
    simpa [Matrix.conjTranspose_apply, Complex.star_def] using h
  have h10im : (H 1 0).im = -(H 0 1).im := by
    have h := congrArg Complex.im (congrFun (congrFun hH 0) 1)
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  fin_cases μ <;>
    simp [pauli4, sigma1, sigma2, sigma3, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, h00, h11, h10re, h10im]

private lemma herm_eq_sum_pauli4 (H : Mat2C) (hH : Hᴴ = H) :
    paravectorMat (fun μ => ((1 / 2 : ℂ) * (pauli4 μ * H).trace).re) = H := by
  have him : ∀ μ : Fin 4, ((1 / 2 : ℂ) * (pauli4 μ * H).trace).im = 0 :=
    pauli4_trace_herm_im_zero H hH
  have hre_coe : ∀ μ : Fin 4,
      (((1 / 2 : ℂ) * (pauli4 μ * H).trace).re : ℂ) = (1 / 2 : ℂ) * (pauli4 μ * H).trace :=
    fun μ => Complex.ext rfl (him μ).symm
  have hsum :
      paravectorMat (fun μ => ((1 / 2 : ℂ) * (pauli4 μ * H).trace).re) =
        ∑ μ : Fin 4, ((1 / 2 : ℂ) * (pauli4 μ * H).trace) • pauli4 μ := by
    dsimp [paravectorMat]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Complex.coe_smul, hre_coe μ]
  rw [hsum, Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    · simp [pauli4, sigma1, sigma2, sigma3, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Fin.sum_univ_two]
      ring

private lemma paravectorMat_injective : Function.Injective paravectorMat := by
  intro x y hxy
  ext μ
  have h00 := congrArg (fun M : Mat2C => (M 0 0).re) hxy
  have h11 := congrArg (fun M : Mat2C => (M 1 1).re) hxy
  have h01re := congrArg (fun M : Mat2C => (M 0 1).re) hxy
  have h10im := congrArg (fun M : Mat2C => (M 1 0).im) hxy
  dsimp [paravectorMat] at h00 h11 h01re h10im
  simp [Fin.sum_univ_four, pauli4, sigma1, sigma2, sigma3, Complex.real_smul]
    at h00 h11 h01re h10im
  fin_cases μ <;> (dsimp; linarith)

theorem paravectorMat_lorentzDilation (M : Mat2C) (x : Fin 4 → ℝ) :
    paravectorMat ((lorentzDilationMat M).mulVec x) = M * paravectorMat x * Mᴴ := by
  have hmul : M * paravectorMat x * Mᴴ =
      ∑ ν : Fin 4, (x ν : ℂ) • (M * pauli4 ν * Mᴴ) := by
    dsimp [paravectorMat]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_assoc]
  have hbasis : ∀ ν : Fin 4,
      paravectorMat (fun μ => lorentzDilationMat M μ ν) = M * pauli4 ν * Mᴴ := by
    intro ν
    have hHerm : (M * pauli4 ν * Mᴴ)ᴴ = M * pauli4 ν * Mᴴ := by
      simp [Matrix.conjTranspose_mul, pauli4_hermitian ν, mul_assoc]
    have hEq := herm_eq_sum_pauli4 (M * pauli4 ν * Mᴴ) hHerm
    simpa [lorentzDilationMat, mul_assoc] using hEq
  rw [hmul]
  dsimp [paravectorMat, Matrix.mulVec, dotProduct]
  calc
    ∑ μ : Fin 4, (∑ ν : Fin 4, lorentzDilationMat M μ ν * x ν : ℝ) • pauli4 μ
        = ∑ μ : Fin 4, ∑ ν : Fin 4, ((x ν : ℂ) • ((lorentzDilationMat M μ ν : ℂ) • pauli4 μ)) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [← Complex.coe_smul]
          push_cast
          rw [mul_comm, mul_smul]
    _ = ∑ ν : Fin 4, (x ν : ℂ) • (∑ μ : Fin 4, (lorentzDilationMat M μ ν : ℂ) • pauli4 μ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [← Finset.smul_sum]
    _ = ∑ ν : Fin 4, (x ν : ℂ) • (M * pauli4 ν * Mᴴ) := by
          refine Finset.sum_congr rfl fun ν _ => by
            congr 1
            exact hbasis ν

theorem lorentzDilationMat_one : lorentzDilationMat (1 : Mat2C) = 1 := by
  ext μ ν
  have hcol : paravectorMat (fun μ => lorentzDilationMat (1 : Mat2C) μ ν) =
      paravectorMat (fun μ => (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) := by
    have h1 := paravectorMat_lorentzDilation (1 : Mat2C) (fun μ => if μ = ν then (1 : ℝ) else 0)
    have h2 : (lorentzDilationMat (1 : Mat2C)).mulVec (fun μ => if μ = ν then (1 : ℝ) else 0) =
        fun μ => lorentzDilationMat (1 : Mat2C) μ ν := by
      ext μ; simp [Matrix.mulVec, dotProduct]
    have h3 : paravectorMat (fun μ => if μ = ν then (1 : ℝ) else 0) = pauli4 ν := by
      dsimp [paravectorMat]; simp
    have h4 : paravectorMat (fun μ => (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) = pauli4 ν := by
      dsimp [paravectorMat]; simp [Matrix.one_apply, eq_comm]
    rw [h2, h3, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at h1
    exact h1.trans h4.symm
  exact congrFun (paravectorMat_injective hcol) μ

theorem lorentzDilationMat_mul (M N : Mat2C) :
    lorentzDilationMat (M * N) = lorentzDilationMat M * lorentzDilationMat N := by
  ext μ ν
  have hcol : paravectorMat (fun μ => lorentzDilationMat (M * N) μ ν) =
      paravectorMat (fun μ => (lorentzDilationMat M * lorentzDilationMat N) μ ν) := by
    let e : Fin 4 → ℝ := fun k => if k = ν then (1 : ℝ) else 0
    have hl : (lorentzDilationMat (M * N)).mulVec e =
        fun μ => lorentzDilationMat (M * N) μ ν := by
      ext μ; simp [e, Matrix.mulVec, dotProduct]
    have hr : (lorentzDilationMat M * lorentzDilationMat N).mulVec e =
        fun μ => (lorentzDilationMat M * lorentzDilationMat N) μ ν := by
      ext μ; simp [e, Matrix.mulVec, dotProduct]
    rw [← hl, ← hr, ← Matrix.mulVec_mulVec, paravectorMat_lorentzDilation,
      paravectorMat_lorentzDilation, paravectorMat_lorentzDilation]
    simp [Matrix.conjTranspose_mul, mul_assoc]
  exact congrFun (paravectorMat_injective hcol) μ

private lemma complex_mul_star (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  apply Complex.ext
  · simp [Complex.normSq_apply]
  · simp [Complex.normSq_apply]
    ring

theorem lorentzDilationMat_minkowskiDot (M : Mat2C) (x : Fin 4 → ℝ) :
    minkowskiDot ((lorentzDilationMat M).mulVec x) ((lorentzDilationMat M).mulVec x) =
      Complex.normSq M.det * minkowskiDot x x := by
  have hdet :
      (paravectorMat ((lorentzDilationMat M).mulVec x)).det =
        (M * paravectorMat x * Mᴴ).det :=
    congrArg Matrix.det (paravectorMat_lorentzDilation M x)
  rw [paravectorMat_det, Matrix.det_mul, Matrix.det_mul, paravectorMat_det,
    Matrix.det_conjTranspose, mul_right_comm, complex_mul_star] at hdet
  norm_cast at hdet

theorem lorentzDilationMat_metric (M : Mat2C) :
    (lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M =
      Complex.normSq M.det • minkowskiEta4 := by
  have hbilin : ∀ u v : Fin 4 → ℝ,
      dotProduct u (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ v) =
        Complex.normSq M.det * dotProduct u (minkowskiEta4 *ᵥ v) := by
    intro u v
    have hdot : ∀ w : Fin 4 → ℝ,
        dotProduct w (minkowskiEta4 *ᵥ w) = minkowskiDot w w := by
      intro w
      simp [minkowskiEta4, minkowskiDot, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four]
      ring
    have hleft :
        ∀ w : Fin 4 → ℝ,
          dotProduct w (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ w) =
            Complex.normSq M.det * minkowskiDot w w := by
      intro w
      calc
        dotProduct w (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ w)
            = dotProduct ((lorentzDilationMat M) *ᵥ w)
                (minkowskiEta4 *ᵥ ((lorentzDilationMat M) *ᵥ w)) := by
              rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
                Matrix.vecMul_transpose]
        _ = minkowskiDot ((lorentzDilationMat M) *ᵥ w) ((lorentzDilationMat M) *ᵥ w) := hdot _
        _ = Complex.normSq M.det * minkowskiDot w w := lorentzDilationMat_minkowskiDot M w
    have hsymA :
        ((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M)ᵀ =
          (lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M := by
      simp [Matrix.transpose_mul, minkowskiEta4, Matrix.diagonal_transpose, mul_assoc]
    have hpolA :
        2 * dotProduct u (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ v) =
          dotProduct (u + v)
            (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ (u + v)) -
          dotProduct u (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ u) -
          dotProduct v (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ v) := by
      have huv :
          dotProduct v (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ u) =
            dotProduct u (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ v) := by
        calc
          dotProduct v (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ u)
              = dotProduct (v ᵥ* ((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M)) u :=
                dotProduct_mulVec v _ u
          _ = dotProduct (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ v) u := by
                rw [← hsymA, Matrix.vecMul_transpose, hsymA]
          _ = dotProduct u (((lorentzDilationMat M)ᵀ * minkowskiEta4 * lorentzDilationMat M) *ᵥ v) :=
                dotProduct_comm _ _
      simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, huv]
      ring
    have hpolB :
        2 * (Complex.normSq M.det * dotProduct u (minkowskiEta4 *ᵥ v)) =
          Complex.normSq M.det * minkowskiDot (u + v) (u + v) -
          Complex.normSq M.det * minkowskiDot u u -
          Complex.normSq M.det * minkowskiDot v v := by
      simp [minkowskiDot, minkowskiEta4, Matrix.mulVec_diagonal, dotProduct,
        Fin.sum_univ_four, Pi.add_apply]
      ring
    rw [hleft (u + v), hleft u, hleft v] at hpolA
    linarith
  ext i j
  have h := hbilin (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single, dotProduct_single, mul_one, one_mul, smul_eq_mul] using h

theorem two_mul_lorentzDilationMat_00 (M : Mat2C) :
    2 * lorentzDilationMat M 0 0 =
      Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
        Complex.normSq (M 1 0) + Complex.normSq (M 1 1) := by
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  dsimp [lorentzDilationMat]
  rw [hhalf]
  simp [pauli4, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem lorentzDilationMat_00_pos (M : Mat2C) (hM : M ≠ 0) :
    0 < lorentzDilationMat M 0 0 := by
  have hsq := two_mul_lorentzDilationMat_00 M
  have hsum_pos : 0 < Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
      Complex.normSq (M 1 0) + Complex.normSq (M 1 1) := by
    by_contra hle
    have ha : 0 ≤ Complex.normSq (M 0 0) := Complex.normSq_nonneg _
    have hb : 0 ≤ Complex.normSq (M 0 1) := Complex.normSq_nonneg _
    have hc : 0 ≤ Complex.normSq (M 1 0) := Complex.normSq_nonneg _
    have hd : 0 ≤ Complex.normSq (M 1 1) := Complex.normSq_nonneg _
    have hnonneg :
        0 ≤ Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
          Complex.normSq (M 1 0) + Complex.normSq (M 1 1) :=
      add_nonneg (add_nonneg (add_nonneg ha hb) hc) hd
    have hzero : Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
        Complex.normSq (M 1 0) + Complex.normSq (M 1 1) = 0 := le_antisymm (not_lt.mp hle) hnonneg
    have h00 : M 0 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have h01 : M 0 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have h10 : M 1 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have h11 : M 1 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    apply hM
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  linarith

private def pauli4ComplexLinEquiv : (Fin 4 → ℂ) ≃ₗ[ℂ] Mat2C where
  toFun c := ∑ μ : Fin 4, c μ • pauli4 μ
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]
  invFun X μ := (1 / 2 : ℂ) * (pauli4 μ * X).trace
  left_inv c := by
    ext μ
    fin_cases μ <;> apply Complex.ext <;>
      · simp [Fin.sum_univ_four, pauli4, sigma1, sigma2, sigma3, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two]
        ring
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      · simp [Fin.sum_univ_four, pauli4, sigma1, sigma2, sigma3, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two]
        ring

private def pauli4Basis : Basis (Fin 4) ℂ Mat2C :=
  (Pi.basisFun ℂ (Fin 4)).map pauli4ComplexLinEquiv

private def mat2StdLinEquiv : (Fin 2 × Fin 2 → ℂ) ≃ₗ[ℂ] Mat2C where
  toFun v i j := v (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun X p := X p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

private def std2Basis : Basis (Fin 2 × Fin 2) ℂ Mat2C :=
  (Pi.basisFun ℂ (Fin 2 × Fin 2)).map mat2StdLinEquiv

private lemma pauli4Basis_apply (ν : Fin 4) : pauli4Basis ν = pauli4 ν := by
  simp [pauli4Basis, Basis.map_apply, Pi.basisFun_apply, pauli4ComplexLinEquiv]

private lemma pauli4Basis_repr_apply (X : Mat2C) (μ : Fin 4) :
    pauli4Basis.repr X μ = (1 / 2 : ℂ) * (pauli4 μ * X).trace := by
  simp [pauli4Basis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr,
    pauli4ComplexLinEquiv]

private lemma mat2StdLinEquiv_apply (v : Fin 2 × Fin 2 → ℂ) (i j : Fin 2) :
    mat2StdLinEquiv v i j = v (i, j) := rfl

private lemma std2Basis_apply (p : Fin 2 × Fin 2) (i j : Fin 2) :
    std2Basis p i j = if (i, j) = p then (1 : ℂ) else 0 := by
  change mat2StdLinEquiv ((Pi.basisFun ℂ (Fin 2 × Fin 2)) p) i j =
    if (i, j) = p then (1 : ℂ) else 0
  rw [mat2StdLinEquiv_apply, Pi.basisFun_apply, Pi.single_apply]

private lemma std2Basis_repr_apply (X : Mat2C) (p : Fin 2 × Fin 2) :
    std2Basis.repr X p = X p.1 p.2 := by
  simp [std2Basis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, mat2StdLinEquiv]

private def leftMulMatLin (M : Mat2C) : Mat2C →ₗ[ℂ] Mat2C where
  toFun X := M * X
  map_add' _ _ := mul_add _ _ _
  map_smul' c x := Algebra.mul_smul_comm c M x

private def rightMulMatLin (M : Mat2C) : Mat2C →ₗ[ℂ] Mat2C where
  toFun X := X * M
  map_add' _ _ := add_mul _ _ _
  map_smul' c x := Algebra.smul_mul_assoc c x M

private def conjActionLin (M : Mat2C) : Mat2C →ₗ[ℂ] Mat2C :=
  (leftMulMatLin M).comp (rightMulMatLin Mᴴ)

/-- Quartic determinant law `det(R(M)) = |det M|⁴` for every `M ∈ M₂(ℂ)`
(Daviau & Bertrand 2018, Eq. 33, p. 255). -/
theorem lorentzDilationMat_det (M : Mat2C) :
    (lorentzDilationMat M).det = (Complex.normSq M.det) ^ 2 := by
  have hpauli_mat :
      LinearMap.toMatrix pauli4Basis pauli4Basis (conjActionLin M) =
        (lorentzDilationMat M).map Complex.ofRealHom := by
    ext μ ν
    have hHerm : (M * pauli4 ν * Mᴴ)ᴴ = M * pauli4 ν * Mᴴ := by
      simp [Matrix.conjTranspose_mul, pauli4_hermitian ν, mul_assoc]
    have him := pauli4_trace_herm_im_zero (M * pauli4 ν * Mᴴ) hHerm μ
    have hrepr :
        (pauli4Basis.repr ((conjActionLin M) (pauli4Basis ν))) μ =
          ((1 / 2 : ℂ) * (pauli4 μ * (M * pauli4 ν * Mᴴ)).trace) := by
      rw [pauli4Basis_apply, conjActionLin, LinearMap.comp_apply, rightMulMatLin, leftMulMatLin]
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [pauli4Basis_repr_apply, mul_assoc]
    rw [LinearMap.toMatrix_apply, hrepr]
    apply Complex.ext
    · simp [lorentzDilationMat, mul_assoc]
    · simpa [mul_assoc] using him
  have hleft_mat :
      LinearMap.toMatrix std2Basis std2Basis (leftMulMatLin M) = M ⊗ₖ (1 : Mat2C) := by
    ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    rw [LinearMap.toMatrix_apply, leftMulMatLin]
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [std2Basis_repr_apply, Matrix.mul_apply]
    simp only [std2Basis_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single b₁]
    · by_cases h2 : a₂ = b₂ <;> simp [h2]
    · intro k _ hk
      simp [hk]
    · intro hm
      exact False.elim (hm (Finset.mem_univ _))
  have hright_mat :
      LinearMap.toMatrix std2Basis std2Basis (rightMulMatLin Mᴴ) = (1 : Mat2C) ⊗ₖ (Mᴴ)ᵀ := by
    ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    rw [LinearMap.toMatrix_apply, rightMulMatLin]
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [std2Basis_repr_apply, Matrix.mul_apply]
    simp only [std2Basis_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.transpose_apply]
    rw [Finset.sum_eq_single b₂]
    · by_cases h1 : a₁ = b₁ <;> simp [h1]
    · intro k _ hk
      simp [hk]
    · intro hm
      exact False.elim (hm (Finset.mem_univ _))
  have hdetL : LinearMap.det (leftMulMatLin M) = M.det ^ 2 := by
    rw [← LinearMap.det_toMatrix std2Basis (leftMulMatLin M), hleft_mat, Matrix.det_kronecker]
    simp
  have hdetR : LinearMap.det (rightMulMatLin Mᴴ) = (star M.det) ^ 2 := by
    rw [← LinearMap.det_toMatrix std2Basis (rightMulMatLin Mᴴ), hright_mat, Matrix.det_kronecker]
    simp [Matrix.det_transpose, Matrix.det_conjTranspose]
  have hdetConj :
      ((lorentzDilationMat M).det : ℂ) = LinearMap.det (conjActionLin M) := by
    rw [← LinearMap.det_toMatrix pauli4Basis (conjActionLin M), hpauli_mat,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.ofRealHom_eq_coe]
  have hcomp :
      LinearMap.det (conjActionLin M) =
        LinearMap.det (leftMulMatLin M) * LinearMap.det (rightMulMatLin Mᴴ) :=
    (LinearMap.det : (Mat2C →ₗ[ℂ] Mat2C) →* ℂ).map_mul (leftMulMatLin M) (rightMulMatLin Mᴴ)
  rw [hcomp, hdetL, hdetR] at hdetConj
  have hnorm :
      (M.det ^ 2 * (star M.det) ^ 2) = (((Complex.normSq M.det) ^ 2 : ℝ) : ℂ) := by
    calc
      M.det ^ 2 * (star M.det) ^ 2 = (M.det * star M.det) ^ 2 := by ring
      _ = ((Complex.normSq M.det : ℂ)) ^ 2 := by rw [complex_mul_star]
      _ = (((Complex.normSq M.det) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  exact Complex.ofReal_injective (hdetConj.trans hnorm)

/-- Double cover `SL(2,ℂ) → SO⁺(1,3)`: every `M ∈ SL(2,ℂ)` sends `minkowskiEta4` to itself,
has determinant `1`, has strictly positive `(0, 0)` entry, satisfies `R(-M) = R(M)`, and
has exact kernel `{±I₂}`. -/
theorem sl2c_double_cover_soPlus13 (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    ((lorentzDilationMat M.1)ᵀ * minkowskiEta4 * lorentzDilationMat M.1 = minkowskiEta4) ∧
    ((lorentzDilationMat M.1).det = 1) ∧
    (0 < lorentzDilationMat M.1 0 0) ∧
    (lorentzDilationMat (-M.1) = lorentzDilationMat M.1) ∧
    (lorentzDilationMat M.1 = 1 ↔ M.1 = 1 ∨ M.1 = -1) := by
  have hdet1 : Complex.normSq M.1.det = 1 := by
    rw [M.prop, Complex.normSq_one]
  have hMne0 : M.1 ≠ 0 := by
    intro h0
    have hdet0 := M.prop
    rw [h0, Matrix.det_zero] at hdet0
    exact zero_ne_one hdet0
  refine ⟨?_, ?_, lorentzDilationMat_00_pos M.1 hMne0, ?_, ?_⟩
  · simpa [hdet1] using lorentzDilationMat_metric M.1
  · rw [lorentzDilationMat_det M.1, hdet1, one_pow]
  · ext μ ν
    simp [lorentzDilationMat]
  · constructor
    · intro hR
      have hconj : ∀ μ : Fin 4, M.1 * pauli4 μ * M.1ᴴ = pauli4 μ := by
        intro μ
        have h1 := paravectorMat_lorentzDilation M.1 (fun k => if k = μ then (1 : ℝ) else 0)
        rw [hR, Matrix.one_mulVec] at h1
        have hp : paravectorMat (fun k => if k = μ then (1 : ℝ) else 0) = pauli4 μ := by
          dsimp [paravectorMat]; simp
        rw [hp] at h1
        exact h1.symm
      have hunitR : M.1 * M.1ᴴ = 1 := by
        simpa [pauli4] using hconj 0
      have hunitL : M.1ᴴ * M.1 = 1 := _root_.mul_eq_one_comm.mp hunitR
      have hcomm : ∀ μ : Fin 4, M.1 * pauli4 μ = pauli4 μ * M.1 := by
        intro μ
        calc
          M.1 * pauli4 μ = (M.1 * pauli4 μ) * (M.1ᴴ * M.1) := by rw [hunitL, mul_one]
          _ = (M.1 * pauli4 μ * M.1ᴴ) * M.1 := by simp [mul_assoc]
          _ = pauli4 μ * M.1 := by rw [hconj μ]
      have hc3 := hcomm 3
      have hc1 := hcomm 1
      have h01_eq := congrFun (congrFun hc3 0) 1
      have h10_eq := congrFun (congrFun hc3 1) 0
      have hdiag_eq := congrFun (congrFun hc1 0) 1
      simp only [pauli4, sigma3, sigma1, Matrix.cons_val, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply] at h01_eq h10_eq hdiag_eq
      have h01 : M.1 0 1 = 0 := by
        have h : -(M.1 0 1) = M.1 0 1 := by simpa using h01_eq
        calc
          M.1 0 1 = (1 / 2 : ℂ) * (M.1 0 1 + M.1 0 1) := by ring
          _ = (1 / 2 : ℂ) * (-(M.1 0 1) + M.1 0 1) := by rw [h]
          _ = 0 := by ring
      have h10 : M.1 1 0 = 0 := by
        have h : M.1 1 0 = -(M.1 1 0) := by simpa using h10_eq
        calc
          M.1 1 0 = (1 / 2 : ℂ) * (M.1 1 0 + M.1 1 0) := by ring
          _ = (1 / 2 : ℂ) * (M.1 1 0 + -(M.1 1 0)) := by rw [← h]
          _ = 0 := by ring
      have hdiag : M.1 0 0 = M.1 1 1 := by
        simpa [h01, h10] using hdiag_eq
      have hdetM := M.prop
      rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero, ← hdiag] at hdetM
      have hpm : M.1 0 0 = 1 ∨ M.1 0 0 = -1 := by
        have hf : (M.1 0 0 - 1) * (M.1 0 0 + 1) = 0 := by
          linear_combination hdetM
        rcases mul_eq_zero.mp hf with h1 | h1
        · left; exact sub_eq_zero.mp h1
        · right; exact eq_neg_of_add_eq_zero_left h1
      rcases hpm with h1 | h1
      · left
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h1, h01, h10, ← hdiag]
      · right
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h1, h01, h10, ← hdiag]
    · rintro (h | h)
      · rw [h, lorentzDilationMat_one]
      · rw [h]
        have hstep : lorentzDilationMat (-(1 : Mat2C)) = lorentzDilationMat (1 : Mat2C) := by
          ext μ ν
          simp [lorentzDilationMat]
        exact hstep.trans lorentzDilationMat_one

end InfoGeometry.Clifford.DaviauBertrandCl3LorentzDilation
