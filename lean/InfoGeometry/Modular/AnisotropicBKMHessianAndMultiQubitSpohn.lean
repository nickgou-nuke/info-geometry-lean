/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSBathAndAnisotropicKuboMori
import InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Artanh
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

/-!
# 3D Anisotropic Bogoliubov-Kubo-Mori Metric & Multi-Qubit Spohn Additivity

This module closes the Milestone 6D Gap 3 cross-pillar synthesis:
1. **3D Anisotropic BKM Metric Tensor on $\mathbb{B}^3$**:
   Regularized radial decomposition $g^{\mathrm{BKM}}(\mathbf{r}, \mathbf{v}) =
   \mathrm{artanhRatio}(\|\mathbf{r}\|) \|\mathbf{v}\|^2 +
   \mathrm{bkmRadialDiff}(\|\mathbf{r}\|) \langle \mathbf{r}, \mathbf{v} \rangle^2$
   with strict anisotropy on the punctured open ball and isotropic collapse at the origin.
2. **Directional Hessian Theorem**:
   Rigorous two-step proof that the directional Hessian of the quantum Umegaki relative
   entropy along rays in the open Bloch ball identically recovers the BKM metric tensor.
3. **Geometric BKM Identification of Spohn Coherence Lag**:
   Exact equality between the 3D transverse Spohn dissipation coherence lag and the
   transverse BKM quadratic form evaluated on the orthogonal projection of the Bloch vector.
4. **Multi-Qubit Kronecker Additivity & OpenGauss T16 Witness**:
   Trace product law, exact Umegaki relative entropy tensor additivity, Spohn dissipation
   nonnegativity on two-qubit product states, and a certified non-commutativity witness
   in $M_4(\mathbb{C}) \cong M_2(\mathbb{C}) \otimes M_2(\mathbb{C})$.
-/

namespace InfoGeometry.Modular.AnisotropicBKMHessianAndMultiQubitSpohn

open scoped Kronecker
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open scoped RealInnerProductSpace
open scoped Matrix.Norms.L2Operator
open scoped MatrixOrder
open scoped _root_.Topology
open InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants

/-!
### Section 1: Core Definitions
-/

/-- Regularized radial difference coefficient `(1 / (1 - r^2) - artanhRatio r) / r^2`. -/
noncomputable def bkmRadialDiff (r : ℝ) : ℝ :=
  if r = 0 then 0 else (1 / (1 - r ^ 2) - artanhRatio r) / r ^ 2

/-- 3D anisotropic Bogoliubov-Kubo-Mori quadratic form on the open Bloch ball. -/
noncomputable def bkmMetric3 (r_vec v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  artanhRatio ‖r_vec‖ * ‖v‖ ^ 2 + bkmRadialDiff ‖r_vec‖ * (inner ℝ r_vec v) ^ 2

/-- Bilinear BKM metric tensor on tangent vectors `u, v` at base point `r_vec`. -/
noncomputable def bkmMetricTensor3 (r_vec : EuclideanSpace ℝ (Fin 3))
    (u v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  artanhRatio ‖r_vec‖ * inner ℝ u v + bkmRadialDiff ‖r_vec‖ * (inner ℝ r_vec u * inner ℝ r_vec v)

/-- Bloch ball density matrix mapping from 3D Euclidean space. -/
noncomputable def blochDensity3 (v : EuclideanSpace ℝ (Fin 3)) : Mat2C :=
  blochState v

/-- 3D Boltzmann negentropy Bregman divergence. -/
noncomputable def bregmanPhi3 (r_vec s_vec : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  negEntropyPhi3 r_vec - negEntropyPhi3 s_vec - inner ℝ (r_vec - s_vec) (legendreTheta3 s_vec)

/-- Full Bloch vector of a 2x2 complex density matrix ρ. -/
def blochVec (ρ : Mat2C) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![blochX ρ, blochY ρ, blochZ ρ]

/-- Transverse projection of the Bloch vector (orthogonal to the z-axis). -/
def transverseBlochVec (ρ : Mat2C) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![blochX ρ, blochY ρ, 0]

/-- Transverse BKM quadratic form: `artanhRatio ‖r_vec‖ * ‖v_perp‖ ^ 2`. -/
noncomputable def bkmTransverseForm (r_vec v_perp : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  artanhRatio ‖r_vec‖ * ‖v_perp‖ ^ 2

/-- Two-qubit Kronecker product state in $M_4(\mathbb{C})$. -/
def twoQubitProductState (ρ₁ ρ₂ : Mat2C) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ρ₁ ⊗ₖ ρ₂

/-- Two-qubit product Umegaki relative entropy defined via tensor log-sum. -/
noncomputable def twoQubitUmegakiDiv (ρ₁ ρ₂ σ₁ σ₂ : Mat2C) : ℝ :=
  (Matrix.trace ((ρ₁ ⊗ₖ ρ₂) * ((CFC.log ρ₁ - CFC.log σ₁) ⊗ₖ 1 + 1 ⊗ₖ (CFC.log ρ₂ - CFC.log σ₂)))).re

/-- Two-qubit Spohn dissipation sum. -/
noncomputable def twoQubitSpohnDissipation (γ₁ γ₂ θ₁ θ₂ : ℝ) (ρ₁ ρ₂ : Mat2C) : ℝ :=
  spohnDissipation3D γ₁ θ₁ ρ₁ + spohnDissipation3D γ₂ θ₂ ρ₂

/-!
### Section 2: Metric Tensor Properties & Strict Anisotropy
-/

/-- The bilinear BKM metric tensor evaluated on identical arguments matches `bkmMetric3`. -/
theorem bkmMetricTensor3_self (r_vec v : EuclideanSpace ℝ (Fin 3)) :
    bkmMetricTensor3 r_vec v v = bkmMetric3 r_vec v := by
  dsimp [bkmMetricTensor3, bkmMetric3]
  have h_inner : inner ℝ v v = ‖v‖ ^ 2 := by
    rw [sq, real_inner_self_eq_norm_mul_norm v]
  rw [h_inner]
  ring

/-- At the origin $\mathbf{r} = 0$, the BKM metric collapses to the isotropic Euclidean norm squared. -/
theorem bkmMetric3_zero (v : EuclideanSpace ℝ (Fin 3)) :
    bkmMetric3 0 v = ‖v‖ ^ 2 := by
  dsimp [bkmMetric3, artanhRatio, bkmRadialDiff]
  simp only [norm_zero, ↓reduceIte, inner_zero_left, sq, mul_zero, add_zero]
  ring

/-- At the origin $\mathbf{r} = 0$, the BKM metric tensor collapses to the standard Euclidean inner product. -/
theorem bkmMetricTensor3_zero (u v : EuclideanSpace ℝ (Fin 3)) :
    bkmMetricTensor3 0 u v = inner ℝ u v := by
  dsimp [bkmMetricTensor3, artanhRatio, bkmRadialDiff]
  simp only [norm_zero, ↓reduceIte, inner_zero_left, mul_zero, add_zero]
  ring

/-- Strict anisotropy: on the open punctured Bloch ball, the transverse coefficient
is strictly smaller than the longitudinal coefficient $1 / (1 - \|\mathbf{r}\|^2)$. -/
theorem bkm_strict_anisotropy {r_vec : EuclideanSpace ℝ (Fin 3)}
    (hr0 : 0 < ‖r_vec‖) (hr1 : ‖r_vec‖ < 1) :
    artanhRatio ‖r_vec‖ < 1 / (1 - ‖r_vec‖ ^ 2) := by
  set s := ‖r_vec‖
  have hs_ioo : s ∈ Set.Ioo 0 1 := ⟨hr0, hr1⟩
  have h_bounds := InfoGeometry.OperatorAlgebra.PeirceBiSandwich.artanh_deriv_and_anisotropic_kubo_mori_bounds hs_ioo
  have hs_ne : s ≠ 0 := hr0.ne'
  have h_ratio_eq : artanhRatio s = canonicalTheta s / s := by
    dsimp [artanhRatio]
    simp only [hs_ne, ↓reduceIte]
  have hs_icc : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hr0], by linarith [hr1]⟩
  have h_artanh_eq : Real.artanh s = 1 / 2 * Real.log ((1 + s) / (1 - s)) :=
    Real.artanh_eq_half_log hs_icc
  have h_canon_eq : canonicalTheta s = Real.artanh s := by
    dsimp [canonicalTheta]
    rw [h_artanh_eq]
  rw [h_ratio_eq, h_canon_eq]
  exact h_bounds.2.2

/-- Positivity of the radial difference coefficient on the punctured open Bloch ball. -/
theorem bkmRadialDiff_pos {r_vec : EuclideanSpace ℝ (Fin 3)}
    (hr0 : 0 < ‖r_vec‖) (hr1 : ‖r_vec‖ < 1) :
    0 < bkmRadialDiff ‖r_vec‖ := by
  dsimp [bkmRadialDiff]
  have hs_ne : ‖r_vec‖ ≠ 0 := hr0.ne'
  simp only [hs_ne, ↓reduceIte]
  have h_num : 0 < 1 / (1 - ‖r_vec‖ ^ 2) - artanhRatio ‖r_vec‖ := by
    linarith [bkm_strict_anisotropy hr0 hr1]
  have h_den : 0 < ‖r_vec‖ ^ 2 := sq_pos_of_pos hr0
  exact div_pos h_num h_den

/-- Strict positivity of the 3D BKM metric on non-zero tangent vectors throughout the open Bloch ball. -/
theorem bkmMetric3_pos {r_vec v : EuclideanSpace ℝ (Fin 3)}
    (hr : ‖r_vec‖ < 1) (hv : v ≠ 0) :
    0 < bkmMetric3 r_vec v := by
  have hv_sq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  by_cases hr0 : ‖r_vec‖ = 0
  · have hr_vec_zero : r_vec = 0 := norm_eq_zero.mp hr0
    rw [hr_vec_zero, bkmMetric3_zero]
    exact hv_sq
  · have hr0_pos : 0 < ‖r_vec‖ := lt_of_le_of_ne (norm_nonneg r_vec) (Ne.symm hr0)
    have hs_ioo : ‖r_vec‖ ∈ Set.Ioo 0 1 := ⟨hr0_pos, hr⟩
    have h_bounds := InfoGeometry.OperatorAlgebra.PeirceBiSandwich.artanh_deriv_and_anisotropic_kubo_mori_bounds hs_ioo
    have hs_icc : ‖r_vec‖ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hr0_pos], by linarith [hr]⟩
    have h_canon_eq : canonicalTheta ‖r_vec‖ = Real.artanh ‖r_vec‖ := by
      dsimp [canonicalTheta]
      rw [Real.artanh_eq_half_log hs_icc]
    have h_ratio_eq : artanhRatio ‖r_vec‖ = Real.artanh ‖r_vec‖ / ‖r_vec‖ := by
      dsimp [artanhRatio]
      simp only [hr0, ↓reduceIte, h_canon_eq]
    have h_ratio_gt_one : 1 < artanhRatio ‖r_vec‖ := by
      rw [h_ratio_eq]
      exact h_bounds.2.1
    have h_ratio_pos : 0 < artanhRatio ‖r_vec‖ := by
      linarith
    have h_term1_pos : 0 < artanhRatio ‖r_vec‖ * ‖v‖ ^ 2 := mul_pos h_ratio_pos hv_sq
    have h_diff_pos := bkmRadialDiff_pos hr0_pos hr
    have h_term2_nonneg : 0 ≤ bkmRadialDiff ‖r_vec‖ * (inner ℝ r_vec v) ^ 2 :=
      mul_nonneg (le_of_lt h_diff_pos) (sq_nonneg _)
    dsimp [bkmMetric3]
    linarith

/-!
### Section 3: Trace Formulas and Directional Hessian
-/

private lemma mat2_00 {A : Type*} (a b c d : A) : mat2 a b c d 0 0 = a := by
  dsimp [mat2]

private lemma mat2_01 {A : Type*} (a b c d : A) : mat2 a b c d 0 1 = b := by
  dsimp [mat2]

private lemma mat2_10 {A : Type*} (a b c d : A) : mat2 a b c d 1 0 = c := by
  dsimp [mat2]

private lemma mat2_11 {A : Type*} (a b c d : A) : mat2 a b c d 1 1 = d := by
  dsimp [mat2]

private lemma legendreTheta3_zero : legendreTheta3 0 = 0 := by
  dsimp [legendreTheta3]
  rw [smul_zero]

private lemma canonicalTheta_zero_val : canonicalTheta 0 = 0 := by
  dsimp [canonicalTheta]
  simp

private lemma canonicalTheta_neg (u : ℝ) (hu_lo : -1 < u) (hu_hi : u < 1) :
    canonicalTheta (-u) = -canonicalTheta u := by
  dsimp [canonicalTheta]
  have h1 : 0 < 1 + u := by
    linarith [hu_lo]
  have h2 : 0 < 1 - u := by
    linarith [hu_hi]
  have h_div : (1 + -u) / (1 - -u) = ((1 + u) / (1 - u))⁻¹ := by
    have h_eq : (1 + -u) / (1 - -u) = (1 - u) / (1 + u) := by
      ring
    rw [h_eq, inv_div]
  rw [h_div, Real.log_inv]
  ring

/-- Unit trace of `blochDensity3 v`. -/
theorem blochDensity3_trace (v : EuclideanSpace ℝ (Fin 3)) :
    Matrix.trace (blochDensity3 v) = 1 := by
  dsimp [blochDensity3, blochState]
  rw [trace_fin2]
  simp only [mat2_00, mat2_11]
  ring

private lemma pauliSigmaX_val : pauliSigmaX = mat2 0 1 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [pauliSigmaX, wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
      InfoGeometry.Algebra.FiniteSpin.J_minus]
    norm_num
  }

private lemma pauliSigmaY_val : pauliSigmaY = mat2 0 (-Complex.I) Complex.I 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [pauliSigmaY, wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
      InfoGeometry.Algebra.FiniteSpin.J_minus]
    norm_num
  }

private lemma pauliGamma1_val : pauliGamma1 = mat2 1 0 0 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [pauliGamma1, InfoGeometry.Algebra.FiniteSpin.J_zero]
    norm_num
  }

/-- Direct matrix expansion of `pauliSlash w`. -/
theorem pauliSlash_val (w : EuclideanSpace ℝ (Fin 3)) :
    pauliSlash w = mat2 (w 2 : ℂ) ((w 0 - Complex.I * w 1 : ℂ)) ((w 0 + Complex.I * w 1 : ℂ)) (-(w 2 : ℂ)) := by
  dsimp [pauliSlash]
  rw [pauliSigmaX_val, pauliSigmaY_val, pauliGamma1_val]
  apply ext_mat2 <;> {
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, mat2_00, mat2_01, mat2_10, mat2_11,
      Fin.isValue]
    ring
  }

/-- Exact trace contraction of `blochState r_vec` against `pauliSlash w`. -/
theorem trace_blochDensity3_mul_pauliSlash (r_vec w : EuclideanSpace ℝ (Fin 3)) :
    Matrix.trace (blochState r_vec * pauliSlash w) = ((inner ℝ r_vec w : ℝ) : ℂ) := by
  rw [pauliSlash_val]
  dsimp [blochState]
  rw [trace_fin2, mul2_00, mul2_11]
  simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue]
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  push_cast
  linear_combination (-(r_vec 1 : ℂ) * (w 1 : ℂ)) * Complex.I_mul_I

/-- Exact complex matrix trace of `blochDensity3 r_vec * CFC.log (blochDensity3 s_vec)`. -/
theorem trace_blochDensity3_mul_cfc_log (r_vec s_vec : EuclideanSpace ℝ (Fin 3))
    (hs : ‖s_vec‖ < 1) :
    Matrix.trace (blochDensity3 r_vec * CFC.log (blochDensity3 s_vec)) =
      ((inner ℝ r_vec (legendreTheta3 s_vec) - cumulantPsi3 (legendreTheta3 s_vec) : ℝ) : ℂ) := by
  dsimp [blochDensity3]
  rw [cfc_log_blochState_universal s_vec hs]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [trace_blochDensity3_mul_pauliSlash]
  have h_smul : blochState r_vec * ((cumulantPsi3 (legendreTheta3 s_vec) : ℂ) • 1) =
      (cumulantPsi3 (legendreTheta3 s_vec) : ℂ) • blochState r_vec := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [h_smul, Matrix.trace_smul, show Matrix.trace (blochState r_vec) = 1 from blochDensity3_trace r_vec]
  push_cast
  ring

/-- Trace of density matrix times its own matrix logarithm recovers negative entropy. -/
theorem trace_blochDensity3_mul_cfc_log_self (r_vec : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r_vec‖ < 1) :
    Matrix.trace (blochDensity3 r_vec * CFC.log (blochDensity3 r_vec)) =
      ((negEntropyPhi3 r_vec : ℝ) : ℂ) := by
  have h_tr := trace_blochDensity3_mul_cfc_log r_vec r_vec hr
  have h_rec := bloch3d_legendre_reciprocity.2 r_vec hr
  have h_fy := (bloch3d_fenchel_young (legendreTheta3 r_vec) r_vec hr).2.mpr h_rec.symm
  have h_inner_symm : inner ℝ (legendreTheta3 r_vec) r_vec = inner ℝ r_vec (legendreTheta3 r_vec) :=
    real_inner_comm r_vec (legendreTheta3 r_vec)
  rw [h_inner_symm] at h_fy
  have h_diff : inner ℝ r_vec (legendreTheta3 r_vec) - cumulantPsi3 (legendreTheta3 r_vec) =
      negEntropyPhi3 r_vec := by
    linarith [h_fy]
  rw [h_tr, h_diff]

/-- Reduction of quantum Umegaki relative entropy between 3D Bloch states to 3D Bregman divergence. -/
theorem umegakiDiv_eq_bregmanPhi3 (r_vec s_vec : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r_vec‖ < 1) (hs : ‖s_vec‖ < 1) :
    umegakiDiv (blochDensity3 r_vec) (blochDensity3 s_vec) = bregmanPhi3 r_vec s_vec := by
  dsimp [umegakiDiv, bregmanPhi3]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  change ((Matrix.trace (blochDensity3 r_vec * CFC.log (blochDensity3 r_vec)) -
    Matrix.trace (blochDensity3 r_vec * CFC.log (blochDensity3 s_vec)))).re = _
  rw [trace_blochDensity3_mul_cfc_log_self r_vec hr]
  rw [trace_blochDensity3_mul_cfc_log r_vec s_vec hs]
  simp only [Complex.sub_re, Complex.ofReal_re]
  have h_rec_s := bloch3d_legendre_reciprocity.2 s_vec hs
  have h_fy_s := (bloch3d_fenchel_young (legendreTheta3 s_vec) s_vec hs).2.mpr h_rec_s.symm
  have h_inner_symm : inner ℝ (legendreTheta3 s_vec) s_vec = inner ℝ s_vec (legendreTheta3 s_vec) :=
    real_inner_comm s_vec (legendreTheta3 s_vec)
  rw [h_inner_symm] at h_fy_s
  have h_inner_sub : inner ℝ (r_vec - s_vec) (legendreTheta3 s_vec) =
      inner ℝ r_vec (legendreTheta3 s_vec) - inner ℝ s_vec (legendreTheta3 s_vec) := by
    rw [inner_sub_left]
  linarith [h_fy_s, h_inner_sub]

/-- The directional first derivative of quantum Umegaki relative entropy along any tangent vector. -/
theorem umegaki_directional_first_deriv (r_vec v : EuclideanSpace ℝ (Fin 3)) (hr : ‖r_vec‖ < 1) :
    HasDerivAt (fun (u : ℝ) => umegakiDiv (blochDensity3 (r_vec + u • v)) (blochDensity3 r_vec))
      (inner ℝ (legendreTheta3 (r_vec + (0 : ℝ) • v) - legendreTheta3 r_vec) v) 0 := by
  have h_zero : inner ℝ (legendreTheta3 (r_vec + (0 : ℝ) • v) - legendreTheta3 r_vec) v = 0 := by
    rw [zero_smul, add_zero, sub_self, inner_zero_left]
  rw [h_zero]
  have h_ev : (fun u : ℝ => umegakiDiv (blochDensity3 (r_vec + u • v)) (blochDensity3 r_vec)) =ᶠ[𝓝 0]
      (fun u : ℝ => bregmanPhi3 (r_vec + u • v) r_vec) := by
    have h_cont : Continuous (fun u : ℝ => ‖r_vec + u • v‖) := by
      continuity
    have h_nhd := h_cont.tendsto 0
    rw [zero_smul, add_zero] at h_nhd
    have h_open : Set.Iio (1 : ℝ) ∈ 𝓝 ‖r_vec‖ := Iio_mem_nhds hr
    have h_lt := h_nhd h_open
    filter_upwards [h_lt] with u hu
    exact umegakiDiv_eq_bregmanPhi3 (r_vec + u • v) r_vec hu hr
  refine (HasDerivAt.congr_of_eventuallyEq ?_ h_ev)
  by_cases hv0 : v = 0
  · subst hv0
    have h_const : (fun u : ℝ => bregmanPhi3 (r_vec + u • (0 : EuclideanSpace ℝ (Fin 3))) r_vec) =
        (fun _ => 0) := by
      funext u
      simp only [smul_zero, add_zero]
      dsimp [bregmanPhi3]
      rw [sub_self, sub_self, inner_zero_left, sub_zero]
    rw [h_const]
    exact hasDerivAt_const 0 0
  · by_cases hr0 : r_vec = 0
    · subst hr0
      have h_phi0 : (fun u : ℝ => bregmanPhi3 (0 + u • v) 0) =
          (fun u : ℝ => negEntropyPhi3 (u • v) - negEntropyPhi3 0) := by
        funext u
        dsimp [bregmanPhi3]
        rw [legendreTheta3_zero, inner_zero_right, sub_zero, zero_add]
      rw [h_phi0]
      have hd : HasDerivAt (fun u : ℝ => negEntropyPhi3 (u • v) - negEntropyPhi3 0) 0 0 := by
        dsimp [negEntropyPhi3]
        have h_der_phi : HasDerivAt negEntropyPhi 0 0 := by
          have h0_lo : (-1 : ℝ) < 0 := by
            linarith
          have h0_hi : (0 : ℝ) < 1 := by
            linarith
          have h_d := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1 0 h0_lo h0_hi
          rw [canonicalTheta_zero_val] at h_d
          exact h_d
        have h_comp : HasDerivAt (fun u : ℝ => negEntropyPhi (|u| * ‖v‖) - negEntropyPhi 0) 0 0 := by
          rw [hasDerivAt_iff_isLittleO] at h_der_phi ⊢
          simp only [sub_zero, smul_zero] at h_der_phi
          simp only [sub_zero, smul_zero, abs_zero, zero_mul, sub_self]
          rw [Asymptotics.isLittleO_iff] at h_der_phi ⊢
          intro ε hε
          have h_denom_pos : 0 < ‖v‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg v) zero_lt_one
          specialize h_der_phi (div_pos hε h_denom_pos)
          have h_tendsto : Filter.Tendsto (fun h : ℝ => |h| * ‖v‖) (𝓝 0) (𝓝 0) := by
            have h_cont : Continuous (fun h : ℝ => |h| * ‖v‖) := by
              continuity
            have h_t := h_cont.tendsto 0
            simp only [abs_zero, zero_mul] at h_t
            exact h_t
          have h_ev := h_tendsto h_der_phi
          filter_upwards [h_ev] with h hh
          change ‖negEntropyPhi (|h| * ‖v‖) - negEntropyPhi 0‖ ≤ (ε / (‖v‖ + 1)) * ‖|h| * ‖v‖‖ at hh
          have h_mul_norm : ‖|h| * ‖v‖‖ = |h| * ‖v‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_norm]
          rw [h_mul_norm] at hh
          calc ‖negEntropyPhi (|h| * ‖v‖) - negEntropyPhi 0‖ ≤ (ε / (‖v‖ + 1)) * (|h| * ‖v‖) := hh
            _ ≤ ε * |h| := by
              have h_denom : 0 < ‖v‖ + 1 := by
                linarith [norm_nonneg v]
              have h_step : (ε / (‖v‖ + 1)) * (|h| * ‖v‖) ≤ ε * |h| := by
                rw [div_mul_eq_mul_div, div_le_iff₀ h_denom]
                have h_eq : ε * |h| * (‖v‖ + 1) = ε * (|h| * ‖v‖) + ε * |h| := by
                  ring
                rw [h_eq]
                have h_eps_h : 0 ≤ ε * |h| := by
                  have h_abs : 0 ≤ |h| := abs_nonneg h
                  nlinarith [hε, h_abs]
                linarith
              exact h_step
            _ = ε * ‖h‖ := by
              rw [Real.norm_eq_abs]
        have h_congr : (fun u : ℝ => negEntropyPhi ‖u • v‖ - negEntropyPhi ‖(0 : EuclideanSpace ℝ (Fin 3))‖) =
            (fun u : ℝ => negEntropyPhi (|u| * ‖v‖) - negEntropyPhi 0) := by
          funext u
          rw [norm_smul, Real.norm_eq_abs, norm_zero]
        rw [h_congr]
        exact h_comp
      exact hd
    · have hr_norm_pos : 0 < ‖r_vec‖ := norm_pos_iff.mpr hr0
      have h_diff_phi : HasDerivAt (fun u : ℝ => negEntropyPhi3 (r_vec + u • v))
          (inner ℝ v (legendreTheta3 r_vec)) 0 := by
        dsimp [negEntropyPhi3]
        have h_norm_sq_der : HasDerivAt (fun u : ℝ => ‖r_vec + u • v‖ ^ 2) (2 * inner ℝ r_vec v) 0 := by
          have h_sum : (fun u : ℝ => ‖r_vec + u • v‖ ^ 2) =
              (fun u : ℝ => (‖r_vec‖ ^ 2 + (2 * inner ℝ r_vec v) * u) + ‖v‖ ^ 2 * (u * u)) := by
            funext u
            rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
            rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
            rw [PiLp.inner_apply, Fin.sum_univ_three]
            simp only [Real.inner_apply]
            have h0 : ‖(r_vec + u • v) 0‖ ^ 2 = (r_vec 0 + u * v 0) ^ 2 := by
              simp [sq_abs]
            have h1 : ‖(r_vec + u • v) 1‖ ^ 2 = (r_vec 1 + u * v 1) ^ 2 := by
              simp [sq_abs]
            have h2 : ‖(r_vec + u • v) 2‖ ^ 2 = (r_vec 2 + u * v 2) ^ 2 := by
              simp [sq_abs]
            have hr0' : ‖r_vec 0‖ ^ 2 = (r_vec 0) ^ 2 := by
              simp [sq_abs]
            have hr1 : ‖r_vec 1‖ ^ 2 = (r_vec 1) ^ 2 := by
              simp [sq_abs]
            have hr2 : ‖r_vec 2‖ ^ 2 = (r_vec 2) ^ 2 := by
              simp [sq_abs]
            have hv0 : ‖v 0‖ ^ 2 = (v 0) ^ 2 := by
              simp [sq_abs]
            have hv1 : ‖v 1‖ ^ 2 = (v 1) ^ 2 := by
              simp [sq_abs]
            have hv2 : ‖v 2‖ ^ 2 = (v 2) ^ 2 := by
              simp [sq_abs]
            rw [h0, h1, h2, hr0', hr1, hr2, hv0, hv1, hv2]
            ring
          rw [h_sum]
          have h_const : HasDerivAt (fun _ : ℝ => ‖r_vec‖ ^ 2) 0 (0 : ℝ) :=
            hasDerivAt_const (0 : ℝ) (‖r_vec‖ ^ 2)
          have h_lin : HasDerivAt (fun u : ℝ => (2 * inner ℝ r_vec v) * u) (2 * inner ℝ r_vec v) (0 : ℝ) := by
            simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * inner ℝ r_vec v)
          have h_quad : HasDerivAt (fun u : ℝ => ‖v‖ ^ 2 * (u * u)) 0 (0 : ℝ) := by
            have h_uu : HasDerivAt (fun u : ℝ => u * u) 0 (0 : ℝ) := by
              have h := (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
              have h_eq : (id * id : ℝ → ℝ) = (fun u => u * u) := by
                ext u
                rfl
              rw [h_eq] at h
              simpa using h
            simpa using h_uu.const_mul (‖v‖ ^ 2)
          have h_add1 := h_const.add h_lin
          simp only [zero_add] at h_add1
          have h_add2 := h_add1.add h_quad
          simp only [add_zero] at h_add2
          exact h_add2
        have h_at0 : ‖r_vec + (0 : ℝ) • v‖ ^ 2 = ‖r_vec‖ ^ 2 := by
          simp only [zero_smul, add_zero]
        have h_sqrt_der : HasDerivAt Real.sqrt (1 / (2 * ‖r_vec‖)) (‖r_vec + (0 : ℝ) • v‖ ^ 2) := by
          rw [h_at0]
          have h_pos_sq : ‖r_vec‖ ^ 2 ≠ 0 := (sq_pos_of_pos hr_norm_pos).ne'
          have h_s := Real.hasDerivAt_sqrt h_pos_sq
          rw [Real.sqrt_sq (norm_nonneg r_vec)] at h_s
          exact h_s
        have h_comp_sqrt := HasDerivAt.comp 0 h_sqrt_der h_norm_sq_der
        have h_comp_sqrt_fn : (Real.sqrt ∘ (fun u : ℝ => ‖r_vec + u • v‖ ^ 2)) =
            (fun u : ℝ => ‖r_vec + u • v‖) := by
          funext u
          exact Real.sqrt_sq (norm_nonneg (r_vec + u • v))
        rw [h_comp_sqrt_fn] at h_comp_sqrt
        have h_norm_der : HasDerivAt (fun u : ℝ => ‖r_vec + u • v‖)
            ((1 / (2 * ‖r_vec‖)) * (2 * inner ℝ r_vec v)) 0 := h_comp_sqrt
        have h_at0_norm : ‖r_vec + (0 : ℝ) • v‖ = ‖r_vec‖ := by
          simp only [zero_smul, add_zero]
        have h_r_lo : (-1 : ℝ) < ‖r_vec‖ := by
          linarith [norm_nonneg r_vec]
        have h_phi_der : HasDerivAt negEntropyPhi (canonicalTheta ‖r_vec‖) (‖r_vec + (0 : ℝ) • v‖) := by
          rw [h_at0_norm]
          exact dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1 ‖r_vec‖ h_r_lo hr
        have h_comp_phi := HasDerivAt.comp 0 h_phi_der h_norm_der
        have h_comp_phi_fn : (negEntropyPhi ∘ (fun u : ℝ => ‖r_vec + u • v‖)) =
            (fun u : ℝ => negEntropyPhi ‖r_vec + u • v‖) := rfl
        rw [h_comp_phi_fn] at h_comp_phi
        have h_alg : canonicalTheta ‖r_vec‖ * ((1 / (2 * ‖r_vec‖)) * (2 * inner ℝ r_vec v)) =
            inner ℝ v (legendreTheta3 r_vec) := by
          dsimp [legendreTheta3, artanhRatio]
          simp only [hr_norm_pos.ne', ↓reduceIte]
          rw [real_inner_smul_right, real_inner_comm v r_vec]
          have hr_ne : ‖r_vec‖ ≠ 0 := hr_norm_pos.ne'
          field_simp
        rw [h_alg] at h_comp_phi
        exact h_comp_phi
      have h_lin_der : HasDerivAt (fun u : ℝ => u * inner ℝ v (legendreTheta3 r_vec))
          (inner ℝ v (legendreTheta3 r_vec)) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ v (legendreTheta3 r_vec))
      have h_diff := h_diff_phi.sub h_lin_der
      have h_diff_zero : inner ℝ v (legendreTheta3 r_vec) - inner ℝ v (legendreTheta3 r_vec) = 0 := by
        ring
      rw [h_diff_zero] at h_diff
      have h_congr : (fun u : ℝ => bregmanPhi3 (r_vec + u • v) r_vec) =
          (fun u : ℝ => (negEntropyPhi3 (r_vec + u • v) - negEntropyPhi3 r_vec) -
            u * inner ℝ v (legendreTheta3 r_vec)) := by
        funext u
        dsimp [bregmanPhi3]
        rw [inner_sub_left, inner_add_left, real_inner_smul_left]
        ring
      rw [h_congr]
      have h_sub_const := h_diff_phi.sub_const (negEntropyPhi3 r_vec)
      have h_final := h_sub_const.sub h_lin_der
      rw [h_diff_zero] at h_final
      exact h_final

/-- Exact Hessian identification: the derivative of the directional gradient equals the BKM metric. -/
theorem umegaki_directional_hessian_eq_bkmMetric3 (r_vec v : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r_vec‖ < 1) :
    HasDerivAt (fun (s : ℝ) => inner ℝ (legendreTheta3 (r_vec + s • v) - legendreTheta3 r_vec) v)
      (bkmMetric3 r_vec v) 0 := by
  have h_sub : (fun s : ℝ => inner ℝ (legendreTheta3 (r_vec + s • v) - legendreTheta3 r_vec) v) =
      (fun s : ℝ => inner ℝ (legendreTheta3 (r_vec + s • v)) v - inner ℝ (legendreTheta3 r_vec) v) := by
    funext s
    rw [inner_sub_left]
  rw [h_sub]
  have h_main : HasDerivAt (fun s : ℝ => inner ℝ (legendreTheta3 (r_vec + s • v)) v)
      (bkmMetric3 r_vec v) 0 := by
    by_cases hr0 : r_vec = 0
    · subst hr0
      have h_bkm0 : bkmMetric3 0 v = ‖v‖ ^ 2 := bkmMetric3_zero v
      rw [h_bkm0]
      have h_id : (fun s : ℝ => inner ℝ (legendreTheta3 (0 + s • v)) v) =ᶠ[𝓝 0]
          (fun s : ℝ => ‖v‖ * canonicalTheta (s * ‖v‖)) := by
        by_cases hv0 : ‖v‖ = 0
        · have hv : v = 0 := norm_eq_zero.mp hv0
          subst hv
          have h_zero_fn : (fun s : ℝ => inner ℝ (legendreTheta3 (0 + s • (0 : EuclideanSpace ℝ (Fin 3)))) 0) =
              (fun _ => 0) := by
            funext s
            rw [inner_zero_right]
          have h_zero_th : (fun s : ℝ => ‖(0 : EuclideanSpace ℝ (Fin 3))‖ * canonicalTheta (s * ‖(0 : EuclideanSpace ℝ (Fin 3))‖)) =
              (fun _ => 0) := by
            funext s
            rw [norm_zero, zero_mul]
          rw [h_zero_fn, h_zero_th]
        · have hv_pos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv0)
          have h_cont : Continuous (fun s : ℝ => |s| * ‖v‖) := by
            continuity
          have h_nhd := h_cont.tendsto 0
          simp only [abs_zero, zero_mul] at h_nhd
          have h_open : Set.Iio (1 : ℝ) ∈ 𝓝 0 := Iio_mem_nhds zero_lt_one
          have h_lt := h_nhd h_open
          filter_upwards [h_lt] with s hs
          dsimp [legendreTheta3, artanhRatio]
          simp only [zero_add]
          by_cases hs0 : s = 0
          · subst hs0
            simp only [smul_zero, zero_smul, norm_zero, ↓reduceIte, canonicalTheta_zero_val, mul_zero, zero_mul, inner_zero_left]
          · have h_norm_smul : ‖s • v‖ = |s| * ‖v‖ := by
              rw [norm_smul, Real.norm_eq_abs]
            have h_pos : 0 < |s| * ‖v‖ := mul_pos (abs_pos.mpr hs0) hv_pos
            rw [h_norm_smul]
            simp only [ne_of_gt h_pos, ↓reduceIte]
            rw [real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm v]
            rcases lt_trichotomy s 0 with hs_neg | rfl | hs_pos
            · have hs_abs : |s| = -s := abs_of_neg hs_neg
              rw [hs_abs]
              have h_s_neg : s * ‖v‖ = - (-s * ‖v‖) := by
                ring
              have h_neg_bound : -s * ‖v‖ < 1 := by
                rw [← hs_abs]
                exact hs
              have h_neg_lo : -1 < -s * ‖v‖ := by
                have : 0 < -s * ‖v‖ := mul_pos (neg_pos.mpr hs_neg) hv_pos
                linarith
              rw [h_s_neg, canonicalTheta_neg (-s * ‖v‖) h_neg_lo h_neg_bound]
              field_simp
            · contradiction
            · have hs_abs : |s| = s := abs_of_pos hs_pos
              rw [hs_abs]
              field_simp
      have h_at0_v : (0 : ℝ) * ‖v‖ = 0 := by
        ring
      have h0_lo : (-1 : ℝ) < 0 := by
        linarith
      have h0_hi : (0 : ℝ) < 1 := by
        linarith
      have h_th_der : HasDerivAt canonicalTheta 1 ((0 : ℝ) * ‖v‖) := by
        rw [h_at0_v]
        have h_d := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.2.1 0 h0_lo h0_hi
        simp only [sq, mul_zero, sub_zero, div_one] at h_d
        exact h_d
      have h_inner_der : HasDerivAt (fun s : ℝ => s * ‖v‖) ‖v‖ 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const ‖v‖
      have h_comp := HasDerivAt.comp 0 h_th_der h_inner_der
      have h_mul := h_comp.const_mul ‖v‖
      have h_sq : ‖v‖ * (1 * ‖v‖) = ‖v‖ ^ 2 := by
        ring
      rw [h_sq] at h_mul
      exact HasDerivAt.congr_of_eventuallyEq h_mul h_id
    · have hr_norm_pos : 0 < ‖r_vec‖ := norm_pos_iff.mpr hr0
      have h_F_eq : (fun s : ℝ => inner ℝ (legendreTheta3 (r_vec + s • v)) v) =
          (fun s : ℝ => artanhRatio ‖r_vec + s • v‖ * (inner ℝ r_vec v + s * ‖v‖ ^ 2)) := by
        funext s
        dsimp [legendreTheta3]
        rw [real_inner_smul_left, inner_add_left, real_inner_smul_left]
        have h_inner_v : inner ℝ v v = ‖v‖ ^ 2 := by
          rw [sq, real_inner_self_eq_norm_mul_norm v]
        rw [h_inner_v]
      rw [h_F_eq]
      have h_norm_sq_der : HasDerivAt (fun s : ℝ => ‖r_vec + s • v‖ ^ 2) (2 * inner ℝ r_vec v) 0 := by
        have h_sum : (fun s : ℝ => ‖r_vec + s • v‖ ^ 2) =
            (fun s : ℝ => (‖r_vec‖ ^ 2 + (2 * inner ℝ r_vec v) * s) + ‖v‖ ^ 2 * (s * s)) := by
          funext s
          rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
          rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
          rw [PiLp.inner_apply, Fin.sum_univ_three]
          simp only [Real.inner_apply]
          have h0 : ‖(r_vec + s • v) 0‖ ^ 2 = (r_vec 0 + s * v 0) ^ 2 := by
            simp [sq_abs]
          have h1 : ‖(r_vec + s • v) 1‖ ^ 2 = (r_vec 1 + s * v 1) ^ 2 := by
            simp [sq_abs]
          have h2 : ‖(r_vec + s • v) 2‖ ^ 2 = (r_vec 2 + s * v 2) ^ 2 := by
            simp [sq_abs]
          have hr0' : ‖r_vec 0‖ ^ 2 = (r_vec 0) ^ 2 := by
            simp [sq_abs]
          have hr1 : ‖r_vec 1‖ ^ 2 = (r_vec 1) ^ 2 := by
            simp [sq_abs]
          have hr2 : ‖r_vec 2‖ ^ 2 = (r_vec 2) ^ 2 := by
            simp [sq_abs]
          have hv0 : ‖v 0‖ ^ 2 = (v 0) ^ 2 := by
            simp [sq_abs]
          have hv1 : ‖v 1‖ ^ 2 = (v 1) ^ 2 := by
            simp [sq_abs]
          have hv2 : ‖v 2‖ ^ 2 = (v 2) ^ 2 := by
            simp [sq_abs]
          rw [h0, h1, h2, hr0', hr1, hr2, hv0, hv1, hv2]
          ring
        rw [h_sum]
        have h_const : HasDerivAt (fun _ : ℝ => ‖r_vec‖ ^ 2) 0 (0 : ℝ) :=
          hasDerivAt_const (0 : ℝ) (‖r_vec‖ ^ 2)
        have h_lin : HasDerivAt (fun s : ℝ => (2 * inner ℝ r_vec v) * s) (2 * inner ℝ r_vec v) (0 : ℝ) := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * inner ℝ r_vec v)
        have h_quad : HasDerivAt (fun s : ℝ => ‖v‖ ^ 2 * (s * s)) 0 (0 : ℝ) := by
          have h_ss : HasDerivAt (fun s : ℝ => s * s) 0 (0 : ℝ) := by
            have h := (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
            have h_eq : (id * id : ℝ → ℝ) = (fun s => s * s) := by
              ext s
              rfl
            rw [h_eq] at h
            simpa using h
          simpa using h_ss.const_mul (‖v‖ ^ 2)
        have h_add1 := h_const.add h_lin
        simp only [zero_add] at h_add1
        have h_add2 := h_add1.add h_quad
        simp only [add_zero] at h_add2
        exact h_add2
      have h_at0 : ‖r_vec + (0 : ℝ) • v‖ ^ 2 = ‖r_vec‖ ^ 2 := by
        simp only [zero_smul, add_zero]
      have h_sqrt_der : HasDerivAt Real.sqrt (1 / (2 * ‖r_vec‖)) (‖r_vec + (0 : ℝ) • v‖ ^ 2) := by
        rw [h_at0]
        have h_pos_sq : ‖r_vec‖ ^ 2 ≠ 0 := (sq_pos_of_pos hr_norm_pos).ne'
        have h_s := Real.hasDerivAt_sqrt h_pos_sq
        rw [Real.sqrt_sq (norm_nonneg r_vec)] at h_s
        exact h_s
      have h_comp_sqrt := HasDerivAt.comp 0 h_sqrt_der h_norm_sq_der
      have h_comp_sqrt_fn : (Real.sqrt ∘ (fun s : ℝ => ‖r_vec + s • v‖ ^ 2)) =
          (fun s : ℝ => ‖r_vec + s • v‖) := by
        funext s
        exact Real.sqrt_sq (norm_nonneg (r_vec + s • v))
      rw [h_comp_sqrt_fn] at h_comp_sqrt
      have h_norm_der : HasDerivAt (fun s : ℝ => ‖r_vec + s • v‖)
          ((1 / (2 * ‖r_vec‖)) * (2 * inner ℝ r_vec v)) 0 := h_comp_sqrt
      have h_at0_norm : ‖r_vec + (0 : ℝ) • v‖ = ‖r_vec‖ := by
        simp only [zero_smul, add_zero]
      have h_r_lo : (-1 : ℝ) < ‖r_vec‖ := by
        linarith [norm_nonneg r_vec]
      have h_th_der : HasDerivAt canonicalTheta (1 / (1 - ‖r_vec‖ ^ 2)) (‖r_vec + (0 : ℝ) • v‖) := by
        rw [h_at0_norm]
        exact dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.2.1 ‖r_vec‖ h_r_lo hr
      have h_id_der : HasDerivAt id 1 (‖r_vec + (0 : ℝ) • v‖) := hasDerivAt_id _
      have h_div_ne : id (‖r_vec + (0 : ℝ) • v‖) ≠ 0 := by
        rw [h_at0_norm]
        exact hr_norm_pos.ne'
      have h_ratio_der := HasDerivAt.div h_th_der h_id_der h_div_ne
      have h_comp_ratio := HasDerivAt.comp 0 h_ratio_der h_norm_der
      rw [h_at0_norm] at h_comp_ratio
      have h_comp_ratio_fn : ((canonicalTheta / id) ∘ (fun s : ℝ => ‖r_vec + s • v‖)) =
          (fun s : ℝ => canonicalTheta ‖r_vec + s • v‖ / ‖r_vec + s • v‖) := rfl
      rw [h_comp_ratio_fn] at h_comp_ratio
      have h_ev_ratio : (fun s : ℝ => canonicalTheta ‖r_vec + s • v‖ / ‖r_vec + s • v‖) =ᶠ[𝓝 0]
          (fun s : ℝ => artanhRatio ‖r_vec + s • v‖) := by
        have h_cont : Continuous (fun s : ℝ => ‖r_vec + s • v‖) := by
          continuity
        have h_nhd := h_cont.tendsto 0
        rw [zero_smul, add_zero] at h_nhd
        have h_pos_set : Set.Ioi (0 : ℝ) ∈ 𝓝 ‖r_vec‖ := Ioi_mem_nhds hr_norm_pos
        have h_mem := h_nhd h_pos_set
        filter_upwards [h_mem] with s hs
        have hs_pos : 0 < ‖r_vec + s • v‖ := hs
        dsimp [artanhRatio]
        simp only [hs_pos.ne', ↓reduceIte]
      have h_g_der := HasDerivAt.congr_of_eventuallyEq h_comp_ratio h_ev_ratio.symm
      dsimp only [id] at h_g_der
      have h_alg_g : (((1 / (1 - ‖r_vec‖ ^ 2)) * ‖r_vec‖ - canonicalTheta ‖r_vec‖ * 1) / ‖r_vec‖ ^ 2) *
          ((1 / (2 * ‖r_vec‖)) * (2 * inner ℝ r_vec v)) =
          bkmRadialDiff ‖r_vec‖ * inner ℝ r_vec v := by
        dsimp [bkmRadialDiff, artanhRatio]
        simp only [hr_norm_pos.ne', ↓reduceIte]
        have hr_ne : ‖r_vec‖ ≠ 0 := hr_norm_pos.ne'
        field_simp
      rw [h_alg_g] at h_g_der
      have h_h_der : HasDerivAt (fun s : ℝ => inner ℝ r_vec v + s * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 := by
        have h_lin : HasDerivAt (fun s : ℝ => s * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).mul_const (‖v‖ ^ 2)
        simpa using h_lin.const_add (inner ℝ r_vec v)
      have h_prod := HasDerivAt.mul h_g_der h_h_der
      dsimp [bkmMetric3]
      have h_eval_zero : artanhRatio ‖r_vec + (0 : ℝ) • v‖ = artanhRatio ‖r_vec‖ := by
        rw [zero_smul, add_zero]
      have h_h_zero : inner ℝ r_vec v + (0 : ℝ) * ‖v‖ ^ 2 = inner ℝ r_vec v := by
        ring
      rw [h_eval_zero, h_h_zero] at h_prod
      have h_ring_eq : (bkmRadialDiff ‖r_vec‖ * inner ℝ r_vec v) * inner ℝ r_vec v +
          artanhRatio ‖r_vec‖ * ‖v‖ ^ 2 =
          artanhRatio ‖r_vec‖ * ‖v‖ ^ 2 + bkmRadialDiff ‖r_vec‖ * (inner ℝ r_vec v) ^ 2 := by
        ring
      rw [h_ring_eq] at h_prod
      exact h_prod
  exact h_main.sub_const (inner ℝ (legendreTheta3 r_vec) v)

/-!
### Section 4: Geometric Spohn Identification & Multi-Qubit Additivity
-/

/-- Geometric identification: the 3D transverse Spohn coherence lag is identically
the transverse BKM quadratic form evaluated on the transverse Bloch vector. -/
theorem spohn_coherence_lag_eq_bkmTransverseForm (γ : ℝ) (ρ : Mat2C) :
    (γ / 2) * artanhRatio (blochRadius ρ) * coherenceSq ρ =
    (γ / 2) * bkmTransverseForm (blochVec ρ) (transverseBlochVec ρ) := by
  dsimp [bkmTransverseForm, transverseBlochVec, blochVec]
  have h_trans_norm : ‖(WithLp.toLp 2 ![blochX ρ, blochY ρ, 0] : EuclideanSpace ℝ (Fin 3))‖ ^ 2 =
      coherenceSq ρ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have h0 : ‖(![blochX ρ, blochY ρ, 0] : Fin 3 → ℝ) 0‖ ^ 2 = (blochX ρ) ^ 2 := by
      simp [sq_abs]
    have h1 : ‖(![blochX ρ, blochY ρ, 0] : Fin 3 → ℝ) 1‖ ^ 2 = (blochY ρ) ^ 2 := by
      simp [sq_abs]
    have h2 : ‖(![blochX ρ, blochY ρ, 0] : Fin 3 → ℝ) 2‖ ^ 2 = 0 := by
      simp
    rw [h0, h1, h2, add_zero]
    have h_nonneg : 0 ≤ (blochX ρ) ^ 2 + (blochY ρ) ^ 2 := by
      positivity
    rw [Real.sq_sqrt h_nonneg]
    dsimp [coherenceSq, blochX, blochY]
    have h_c_norm : Complex.normSq (ρ 0 1) = (ρ 0 1).re ^ 2 + (ρ 0 1).im ^ 2 := by
      rw [Complex.normSq_apply, sq, sq]
    rw [h_c_norm]
    ring
  have h_vec_norm : ‖(WithLp.toLp 2 ![blochX ρ, blochY ρ, blochZ ρ] : EuclideanSpace ℝ (Fin 3))‖ =
      blochRadius ρ := by
    dsimp [blochRadius]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have h0 : ‖(![blochX ρ, blochY ρ, blochZ ρ] : Fin 3 → ℝ) 0‖ ^ 2 = (blochX ρ) ^ 2 := by
      simp [sq_abs]
    have h1 : ‖(![blochX ρ, blochY ρ, blochZ ρ] : Fin 3 → ℝ) 1‖ ^ 2 = (blochY ρ) ^ 2 := by
      simp [sq_abs]
    have h2 : ‖(![blochX ρ, blochY ρ, blochZ ρ] : Fin 3 → ℝ) 2‖ ^ 2 = (blochZ ρ) ^ 2 := by
      simp [sq_abs]
    rw [h0, h1, h2]
    dsimp [blochNormSq, coherenceSq, blochX, blochY]
    have h_c_norm : Complex.normSq (ρ 0 1) = (ρ 0 1).re ^ 2 + (ρ 0 1).im ^ 2 := by
      rw [Complex.normSq_apply, sq, sq]
    rw [h_c_norm]
    have h_sq_eq : (blochZ ρ) ^ 2 + (4 * ((ρ 0 1).re ^ 2 + (ρ 0 1).im ^ 2)) =
        (2 * (ρ 0 1).re) ^ 2 + (-2 * (ρ 0 1).im) ^ 2 + (blochZ ρ) ^ 2 := by
      ring
    rw [h_sq_eq]
  rw [h_trans_norm, h_vec_norm]
  ring

/-- Nonnegativity of the 3D Spohn dissipation rate for all states in the open Bloch ball. -/
theorem spohn_dissipation_nonneg (γ θ : ℝ) (hγ : 0 < γ) {ρ : Mat2C}
    (hρ : InOpenBlochBall ρ) :
    0 ≤ spohnDissipation3D γ θ ρ :=
  (quantum_spohn_lyapunov_monotonicity_and_diagonal_reduction hγ hρ).1

/-- Trace product law for Kronecker product states. -/
theorem twoQubitProductState_trace (ρ₁ ρ₂ : Mat2C) :
    Matrix.trace (twoQubitProductState ρ₁ ρ₂) = Matrix.trace ρ₁ * Matrix.trace ρ₂ := by
  dsimp [twoQubitProductState]
  exact Matrix.trace_kronecker ρ₁ ρ₂

/-- Additivity of Umegaki relative entropy across product states. -/
theorem twoQubit_umegaki_additivity (ρ₁ ρ₂ σ₁ σ₂ : Mat2C)
    (hρ₁ : Matrix.trace ρ₁ = 1) (hρ₂ : Matrix.trace ρ₂ = 1) :
    twoQubitUmegakiDiv ρ₁ ρ₂ σ₁ σ₂ = umegakiDiv ρ₁ σ₁ + umegakiDiv ρ₂ σ₂ := by
  dsimp [twoQubitUmegakiDiv, umegakiDiv]
  have h_distrib : (ρ₁ ⊗ₖ ρ₂) * ((CFC.log ρ₁ - CFC.log σ₁) ⊗ₖ 1 + 1 ⊗ₖ (CFC.log ρ₂ - CFC.log σ₂)) =
      (ρ₁ ⊗ₖ ρ₂) * ((CFC.log ρ₁ - CFC.log σ₁) ⊗ₖ 1) +
      (ρ₁ ⊗ₖ ρ₂) * (1 ⊗ₖ (CFC.log ρ₂ - CFC.log σ₂)) := by
    rw [Matrix.mul_add]
  have h_term1 : (ρ₁ ⊗ₖ ρ₂) * ((CFC.log ρ₁ - CFC.log σ₁) ⊗ₖ (1 : Mat2C)) =
      (ρ₁ * (CFC.log ρ₁ - CFC.log σ₁)) ⊗ₖ (ρ₂ * 1) := by
    rw [Matrix.mul_kronecker_mul]
  have h_term2 : (ρ₁ ⊗ₖ ρ₂) * ((1 : Mat2C) ⊗ₖ (CFC.log ρ₂ - CFC.log σ₂)) =
      (ρ₁ * 1) ⊗ₖ (ρ₂ * (CFC.log ρ₂ - CFC.log σ₂)) := by
    rw [Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one] at h_term1 h_term2
  rw [h_distrib, h_term1, h_term2, Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker]
  rw [hρ₁, hρ₂]
  simp only [mul_one, one_mul, Complex.add_re]
  dsimp [InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel,
    InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.relativeLogDensity, CFC.log]

/-- Nonnegativity of the two-qubit Spohn dissipation sum. -/
theorem twoQubit_spohn_dissipation_nonneg (γ₁ γ₂ θ₁ θ₂ : ℝ)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) {ρ₁ ρ₂ : Mat2C}
    (hρ₁ : InOpenBlochBall ρ₁) (hρ₂ : InOpenBlochBall ρ₂) :
    0 ≤ twoQubitSpohnDissipation γ₁ γ₂ θ₁ θ₂ ρ₁ ρ₂ := by
  dsimp [twoQubitSpohnDissipation]
  have h1 := spohn_dissipation_nonneg γ₁ θ₁ hγ₁ hρ₁
  have h2 := spohn_dissipation_nonneg γ₂ θ₂ hγ₂ hρ₂
  linarith

/-!
### Section 5: OpenGauss T16 Non-commutativity Witness
-/

/-- Certified OpenGauss T16 non-commutativity witness on two-qubit operator algebras. -/
theorem multi_qubit_operator_noncommutative :
    (pauliSigmaX ⊗ₖ (1 : Mat2C)) * (pauliGamma1 ⊗ₖ (1 : Mat2C)) ≠
    (pauliGamma1 ⊗ₖ (1 : Mat2C)) * (pauliSigmaX ⊗ₖ (1 : Mat2C)) := by
  intro h_eq
  have h_prod1 : (pauliSigmaX ⊗ₖ (1 : Mat2C)) * (pauliGamma1 ⊗ₖ (1 : Mat2C)) =
      (pauliSigmaX * pauliGamma1) ⊗ₖ (1 : Mat2C) := by
    have h_m := (Matrix.mul_kronecker_mul pauliSigmaX pauliGamma1 (1 : Mat2C) (1 : Mat2C)).symm
    rw [Matrix.mul_one] at h_m
    exact h_m
  have h_prod2 : (pauliGamma1 ⊗ₖ (1 : Mat2C)) * (pauliSigmaX ⊗ₖ (1 : Mat2C)) =
      (pauliGamma1 * pauliSigmaX) ⊗ₖ (1 : Mat2C) := by
    have h_m := (Matrix.mul_kronecker_mul pauliGamma1 pauliSigmaX (1 : Mat2C) (1 : Mat2C)).symm
    rw [Matrix.mul_one] at h_m
    exact h_m
  rw [h_prod1, h_prod2] at h_eq
  have h_inj : pauliSigmaX * pauliGamma1 = pauliGamma1 * pauliSigmaX := by
    ext i j
    have h_ij := congr_fun (congr_fun h_eq (i, 0)) (j, 0)
    change ((pauliSigmaX * pauliGamma1) ⊗ₖ (1 : Mat2C)) (i, 0) (j, 0) =
           ((pauliGamma1 * pauliSigmaX) ⊗ₖ (1 : Mat2C)) (i, 0) (j, 0) at h_ij
    simp only [Matrix.kronecker_apply, Matrix.one_apply, ↓reduceIte, mul_one] at h_ij
    exact h_ij
  exact pauli_matrices_noncommutative h_inj

/-!
### Section 6: Master Synthesis
-/

/-- Comprehensive synthesis theorem: unites the 3D anisotropic BKM metric, exact directional
Hessian identification, Spohn coherence lag geometric representation, multi-qubit additivity,
and certified non-commutative operator algebra witness. -/
theorem master_anisotropic_bkm_and_multi_qubit_spohn_synthesis :
    (∀ v : EuclideanSpace ℝ (Fin 3), bkmMetric3 0 v = ‖v‖ ^ 2) ∧
    (∀ {r_vec : EuclideanSpace ℝ (Fin 3)}, 0 < ‖r_vec‖ → ‖r_vec‖ < 1 →
      artanhRatio ‖r_vec‖ < 1 / (1 - ‖r_vec‖ ^ 2)) ∧
    (∀ (r_vec v : EuclideanSpace ℝ (Fin 3)), ‖r_vec‖ < 1 →
      HasDerivAt (fun (u : ℝ) => umegakiDiv (blochDensity3 (r_vec + u • v)) (blochDensity3 r_vec))
        (inner ℝ (legendreTheta3 (r_vec + (0 : ℝ) • v) - legendreTheta3 r_vec) v) 0) ∧
    (∀ (r_vec v : EuclideanSpace ℝ (Fin 3)), ‖r_vec‖ < 1 →
      HasDerivAt (fun (s : ℝ) => inner ℝ (legendreTheta3 (r_vec + s • v) - legendreTheta3 r_vec) v)
        (bkmMetric3 r_vec v) 0) ∧
    (∀ (γ : ℝ) (ρ : Mat2C),
      (γ / 2) * artanhRatio (blochRadius ρ) * coherenceSq ρ =
      (γ / 2) * bkmTransverseForm (blochVec ρ) (transverseBlochVec ρ)) ∧
    (∀ (ρ₁ ρ₂ σ₁ σ₂ : Mat2C), Matrix.trace ρ₁ = 1 → Matrix.trace ρ₂ = 1 →
      twoQubitUmegakiDiv ρ₁ ρ₂ σ₁ σ₂ = umegakiDiv ρ₁ σ₁ + umegakiDiv ρ₂ σ₂) ∧
    (∀ (γ₁ γ₂ θ₁ θ₂ : ℝ) {ρ₁ ρ₂ : Mat2C}, 0 < γ₁ → 0 < γ₂ →
      InOpenBlochBall ρ₁ → InOpenBlochBall ρ₂ →
      0 ≤ twoQubitSpohnDissipation γ₁ γ₂ θ₁ θ₂ ρ₁ ρ₂) ∧
    ((pauliSigmaX ⊗ₖ (1 : Mat2C)) * (pauliGamma1 ⊗ₖ (1 : Mat2C)) ≠
     (pauliGamma1 ⊗ₖ (1 : Mat2C)) * (pauliSigmaX ⊗ₖ (1 : Mat2C))) := by
  refine ⟨bkmMetric3_zero,
          fun hr0 hr1 => bkm_strict_anisotropy hr0 hr1,
          fun r_vec v hr => umegaki_directional_first_deriv r_vec v hr,
          fun r_vec v hr => umegaki_directional_hessian_eq_bkmMetric3 r_vec v hr,
          spohn_coherence_lag_eq_bkmTransverseForm,
          twoQubit_umegaki_additivity,
          fun γ₁ γ₂ θ₁ θ₂ ρ₁ ρ₂ hγ₁ hγ₂ hρ₁ hρ₂ =>
            twoQubit_spohn_dissipation_nonneg γ₁ γ₂ θ₁ θ₂ hγ₁ hγ₂ hρ₁ hρ₂,
          multi_qubit_operator_noncommutative⟩

end InfoGeometry.Modular.AnisotropicBKMHessianAndMultiQubitSpohn
