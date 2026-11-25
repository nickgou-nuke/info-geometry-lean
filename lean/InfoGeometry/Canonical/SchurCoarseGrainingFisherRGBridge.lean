/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
import InfoGeometry.OperatorAlgebra.CoarseGrainingComposition
import InfoGeometry.Algebra.BlockSchurFactorization
import InfoGeometry.Architecture.MatrixSymmetricConeFisherRao
import InfoGeometry.Probability.GaussianKullbackLeibler
import InfoGeometry.Probability.GaussianTraceLogdet
import InfoGeometry.QuantumContext.PetzDataProcessingMonotonicity

/-!
# Wilson–Gaussian Schur Coarse-Graining, Fisher–Rao Contraction, KL Data Processing, & Peirce RG Tower

This module supplies **Soldering Way IV**: the exact typed bridge unifying four previously
separate families on positive-definite real matrices `Matrix (Fin n) (Fin n) ℝ` without
any commutation, simultaneous diagonalization, or square/rank restriction on the rectangular
coarse-graining map `Q : Matrix (Fin m) (Fin n) ℝ`:

1. **Schur Block Determinant & Loewner Order Toolkit**:
   - `det_coarsePrecision_mul_det_finePrecision`:
     `det (coarsePrecision A R Q) * det (finePrecision A R Q) = det R * det A`.
   - Trace–Loewner positivity & nondegeneracy: `posSemidef_trace_nonneg`,
     `trace_posSemidef_mul_posSemidef_nonneg`, `trace_posDef_mul_posSemidef_eq_zero_iff`.
   - Operator inverse antitonicity `posDef_inv_antitone` (`A ≤ B → B⁻¹ ≤ A⁻¹`) proved via the
     whitening matrix `S = CFC.sqrt A⁻¹` and `eigenvectorUnitary`.
   - Loewner coarse-graining laws: `coarsePrecision_le_obsPrecision`,
     `finePrecision_ge_priorPrecision`, `coarseCovariance_antitone`, `coarsePrecision_monotone`,
     and Schur ratio contraction `schur_pullback_le_ratio` (`Qᵀ R Q ≤ c A → Qᵀ S Q ≤ (c/(1+c)) A`).
2. **Exact Fisher–Rao Coarse-Graining Information Loss & Contraction**:
   - Rectangular congruence pushforward `rectCongruence Q X := Q * X * Qᵀ`, coinciding with
     `MatrixSymmetricCone.congruenceAction` when `m = n`.
   - Exact information-loss identity `fisherRao_coarseGraining_defect_eq` decomposing
     `g_A(X, X) - g_S(Q X Qᵀ, Q X Qᵀ)` as a sum of two nonnegative traces, yielding
     monotonicity `fisherRao_coarseGraining_le`, strict contraction for `X ≠ 0`
     (`fisherRao_coarseGraining_strict_lt`), and geometric contraction
     `fisherRao_coarseGraining_contraction_of_coupling_bound` with factor `(c / (1 + c)) ^ 2`.
3. **Multivariate Gaussian Block-Spin Pushforward & KL Data-Processing Inequality**:
   - `wilsonGaussianBlockSpin_measure_eq`:
     `((𝒩(0, A⁻¹)).map (rectEuclideanCLM Q)) ∗ 𝒩(0, R⁻¹) = 𝒩(0, coarseCovariance A R Q)`.
   - Native Mathlib KL contraction `klDiv_coarseCovariance_le`, clipped-free `toReal` bound
     `toReal_klDiv_coarseCovariance_le`, and trace–logdet monotonicity
     `trace_logdet_coarseCovariance_le`.
4. **Two-Step Rectangular Composition & Multi-Step Iterated RG Contraction Tower**:
   - Two-stage KL and Fisher contraction (`twoStage_klDiv_contraction`,
     `twoStage_fisherRao_contraction`) welded to `CoarseGrainingComposition`.
   - Iterated RG sequences `rgIterPrecision` and `rgIterTangent`, proving KL antitoneness
     (`rgIter_klDiv_antitone`), Fisher antitoneness (`rgIter_fisherRao_antitone`), and
     multi-step geometric decay `(c / (1 + c)) ^ (2 * k)` (`rgIter_fisherRao_geometric_decay`).
5. **Peirce / Causal Pinching Specialization**:
   - Specializes rectangular coarse-graining to `PetzDataProcessingMonotonicity.isCausalProjector`
     and `causalChannel P X = P * X * P`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace InfoGeometry.Canonical.SchurCoarseGrainingFisherRGBridge

open MeasureTheory ProbabilityTheory InformationTheory Matrix WithLp
open InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
open InfoGeometry.Architecture.MatrixSymmetricCone
open InfoGeometry.Probability
open InfoGeometry.QuantumContext
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder

/-! ## Section 1: Schur Block Determinant & Loewner Order Toolkit -/

section SchurDeterminantAndLoewner

private theorem posDef_det_isUnit {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    IsUnit M.det :=
  isUnit_iff_ne_zero.mpr hM.det_pos.ne'

private theorem posDef_transpose {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    Mᵀ = M := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.isHermitian.eq

/-- **Schur Block Determinant Factorization**:
`det (coarsePrecision A R Q) * det (finePrecision A R Q) = det R * det A`
without any commutation hypothesis. -/
theorem det_coarsePrecision_mul_det_finePrecision {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    (coarsePrecision A R Q).det * (finePrecision A R Q).det = R.det * A.det := by
  have hK := finePrecision_posDef Q hA hR
  have hKdet : IsUnit (finePrecision A R Q).det := posDef_det_isUnit hK
  have hRT : Rᵀ = R := posDef_transpose hR
  let M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
    Matrix.fromBlocks R (-(R * Q)) (-(R * Q))ᵀ (finePrecision A R Q)
  have h1 :
      M.det = (coarsePrecision A R Q).det * (finePrecision A R Q).det := by
    have hdet :=
      InfoGeometry.Algebra.BlockSchurFactorization.det_fromBlocks_eq_schur_mul_det
        R (-(R * Q)) (-(R * Q))ᵀ (finePrecision A R Q) (finePrecision A R Q)⁻¹
        (Matrix.nonsing_inv_mul _ hKdet) (Matrix.mul_nonsing_inv _ hKdet)
    have hschur :
        R - (-(R * Q)) * (finePrecision A R Q)⁻¹ * (-(R * Q))ᵀ =
          coarsePrecision A R Q := by
      simp only [Matrix.transpose_neg, Matrix.transpose_mul, hRT,
        Matrix.neg_mul, Matrix.mul_neg, neg_neg, coarsePrecision,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    rwa [hschur] at hdet
  have hM :
      M =
        Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) 0 (-Qᵀ) (1 : Matrix (Fin n) (Fin n) ℝ) *
          Matrix.fromBlocks R 0 0 A *
            Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ) (-Q) 0
              (1 : Matrix (Fin n) (Fin n) ℝ) := by
    dsimp only [M]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul,
      neg_neg]
    congr 1
    · rw [Matrix.transpose_neg, Matrix.transpose_mul, hRT]
    · simp only [finePrecision, Matrix.conjTranspose_eq_transpose_of_trivial, add_comm]
  have h2 : M.det = R.det * A.det := by
    rw [hM]
    simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, one_mul, mul_one]
  exact h1.symm.trans h2

/-- Trace of any real positive semidefinite matrix is nonnegative. -/
theorem posSemidef_trace_nonneg {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) : 0 ≤ P.trace := by
  have htr := hP.1.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at htr
  rw [htr]
  exact Finset.sum_nonneg fun i _ => hP.eigenvalues_nonneg i

/-- Trace of the product of two real positive semidefinite matrices is nonnegative
even when the matrices do not commute. -/
theorem trace_posSemidef_mul_posSemidef_nonneg {n : ℕ}
    {P₁ P₂ : Matrix (Fin n) (Fin n) ℝ}
    (h₁ : P₁.PosSemidef) (h₂ : P₂.PosSemidef) :
    0 ≤ (P₁ * P₂).trace := by
  set S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt P₂
  have hP₂nonneg : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ P₂ :=
    Matrix.nonneg_iff_posSemidef.mpr h₂
  have hSS : S * S = P₂ := CFC.sqrt_mul_sqrt_self P₂ hP₂nonneg
  have hSsa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg P₂)
  have hST : Sᵀ = S := by
    have h : star S = S := hSsa
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have htr : (P₁ * P₂).trace = (S * P₁ * S).trace := by
    rw [← hSS, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have hconj : (S * P₁ * S).PosSemidef := by
    have h := h₁.mul_mul_conjTranspose_same S
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hST] at h
  rw [htr]
  exact posSemidef_trace_nonneg hconj

/-- For `P₁ > 0` and `P₂ ≥ 0`, `Tr(P₁ P₂) = 0` holds iff `P₂ = 0`. -/
theorem trace_posDef_mul_posSemidef_eq_zero_iff {n : ℕ}
    {P₁ P₂ : Matrix (Fin n) (Fin n) ℝ}
    (h₁ : P₁.PosDef) (h₂ : P₂.PosSemidef) :
    (P₁ * P₂).trace = 0 ↔ P₂ = 0 := by
  set S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt P₁
  have hP₁nonneg : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ P₁ :=
    Matrix.nonneg_iff_posSemidef.mpr h₁.posSemidef
  have hSS : S * S = P₁ := CFC.sqrt_mul_sqrt_self P₁ hP₁nonneg
  have hSsa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg P₁)
  have hST : Sᵀ = S := by
    have h : star S = S := hSsa
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hSdet : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hsq : S.det * S.det = P₁.det := by rw [← Matrix.det_mul, hSS]
    rw [h0, mul_zero] at hsq
    exact h₁.det_pos.ne' hsq.symm
  have htr : (P₁ * P₂).trace = (S * P₂ * S).trace := by
    rw [← hSS, ← Matrix.trace_mul_cycle S P₂ S]
  have hconj : (S * P₂ * S).PosSemidef := by
    have h := h₂.mul_mul_conjTranspose_same S
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hST] at h
  rw [htr, hconj.trace_eq_zero_iff]
  constructor
  · intro hSPS
    calc
      P₂ = (S⁻¹ * S) * P₂ * (S * S⁻¹) := by
            rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_nonsing_inv S hSdet,
              Matrix.one_mul, Matrix.mul_one]
      _ = S⁻¹ * (S * P₂ * S) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hSPS, Matrix.mul_zero, Matrix.zero_mul]
  · rintro rfl
    simp

/-- **Loewner Inverse Antitonicity** (`0 < A ≤ B → B⁻¹ ≤ A⁻¹`) proved for real SPD
matrices without commutation using the whitening matrix `CFC.sqrt A⁻¹` and the
spectral theorem. -/
theorem posDef_inv_antitone {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  classical
  have hAdetU : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  set S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt A⁻¹ with hS_def
  have hAinv0 : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ A⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hA.inv.posSemidef
  have hSS : S * S = A⁻¹ := by rw [hS_def]; exact CFC.sqrt_mul_sqrt_self A⁻¹ hAinv0
  have hSsa : IsSelfAdjoint S := by rw [hS_def]; exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A⁻¹)
  have hST : Sᵀ = S := by
    have h : star S = S := hSsa
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hSdet : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hsq : S.det * S.det = A⁻¹.det := by rw [← Matrix.det_mul, hSS]
    rw [h0, mul_zero] at hsq
    exact hA.inv.det_pos.ne' hsq.symm
  have hSunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr hSdet
  have hSmulVecInj : Function.Injective S.mulVec := Matrix.mulVec_injective_of_isUnit hSunit
  have hAcomm : Commute A⁻¹ A := by
    unfold Commute SemiconjBy
    rw [Matrix.nonsing_inv_mul A hAdetU, Matrix.mul_nonsing_inv A hAdetU]
  have hcomm : Commute S A := by rw [hS_def]; exact hAcomm.cfcₙ_nnreal NNReal.sqrt
  have hSAS : S * A * S = 1 := by
    rw [Matrix.mul_assoc, ← hcomm.eq, ← Matrix.mul_assoc, hSS, Matrix.nonsing_inv_mul A hAdetU]
  set C : Matrix (Fin n) (Fin n) ℝ := S * B * S with hC_def
  have hC : C.PosDef := by
    rw [hC_def]
    have h := hB.conjTranspose_mul_mul_same hSmulVecInj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hST] at h
  have hCm1 : (C - 1).PosSemidef := by
    have heq : C - 1 = S * (B - A) * S := by
      rw [hC_def, ← hSAS, Matrix.mul_sub, Matrix.sub_mul]
    rw [heq]
    have h := hAB.mul_mul_conjTranspose_same S
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hST] at h
  set Λ : Fin n → ℝ := hC.1.eigenvalues with hΛ_def
  have hΛpos : ∀ i, 0 < Λ i := fun i => hC.eigenvalues_pos i
  set U : Matrix (Fin n) (Fin n) ℝ := (hC.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    with hU_def
  have hstarU : star U = Uᵀ := by
    rw [hU_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUUt : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hC.1.eigenvectorUnitary
    rwa [Unitary.coe_star, ← hU_def, hstarU] at h
  have hUtU : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hC.1.eigenvectorUnitary
    rwa [← hU_def, hstarU] at h
  have hUtCU : Uᵀ * C * U = Matrix.diagonal Λ := by
    have h := hC.1.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := ℝ)
    rw [Unitary.conjStarAlgAut_star_apply, ← hU_def, hstarU] at h
    rw [h, hΛ_def]
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp]
  have hCspec : C = U * Matrix.diagonal Λ * Uᵀ := by
    calc
      C = (U * Uᵀ) * C * (U * Uᵀ) := by rw [hUUt, Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᵀ * C * U) * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal Λ * Uᵀ := by rw [hUtCU]
  have hdiag_Cm1 : Uᵀ * (C - 1) * U = Matrix.diagonal (fun i => Λ i - 1) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUtCU, hUtU]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hCm1_conj : (Uᵀ * (C - 1) * U).PosSemidef := by
    have h := hCm1.conjTranspose_mul_mul_same U
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hΛge1 : ∀ i, 1 ≤ Λ i := by
    intro i
    have h0 := hCm1_conj.re_dotProduct_nonneg (Pi.single i 1)
    rw [hdiag_Cm1] at h0
    simp only [RCLike.re_to_real, star_trivial, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.diagonal_apply_eq, single_dotProduct, one_mul] at h0
    exact sub_nonneg.mp h0
  have hCinv : C⁻¹ = U * Matrix.diagonal (fun i => (Λ i)⁻¹) * Uᵀ := by
    apply Matrix.inv_eq_right_inv
    calc
      C * (U * Matrix.diagonal (fun i => (Λ i)⁻¹) * Uᵀ)
          = U * (Matrix.diagonal Λ * (Uᵀ * U) * Matrix.diagonal (fun i => (Λ i)⁻¹)) * Uᵀ := by
            conv_lhs => rw [hCspec]
            simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal Λ * Matrix.diagonal (fun i => (Λ i)⁻¹)) * Uᵀ := by
            rw [hUtU, Matrix.mul_one]
      _ = U * 1 * Uᵀ := by
            have hdiag : Matrix.diagonal Λ * Matrix.diagonal (fun i => (Λ i)⁻¹) = 1 := by
              rw [Matrix.diagonal_mul_diagonal]
              ext i j
              by_cases hij : i = j
              · subst hij; simp [(hΛpos i).ne']
              · simp [Matrix.diagonal, hij]
            rw [hdiag]
      _ = 1 := by rw [Matrix.mul_one, hUUt]
  have hone_sub_Cinv : (1 - C⁻¹).PosSemidef := by
    have heq : 1 - C⁻¹ = U * Matrix.diagonal (fun i => 1 - (Λ i)⁻¹) * Uᵀ := by
      calc
        1 - C⁻¹ = U * (1 : Matrix (Fin n) (Fin n) ℝ) * Uᵀ -
            U * Matrix.diagonal (fun i => (Λ i)⁻¹) * Uᵀ := by
              rw [Matrix.mul_one, hUUt, hCinv]
        _ = U * (1 - Matrix.diagonal (fun i => (Λ i)⁻¹)) * Uᵀ := by
              rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = U * Matrix.diagonal (fun i => 1 - (Λ i)⁻¹) * Uᵀ := by
              have hd : (1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.diagonal (fun i => (Λ i)⁻¹) =
                  Matrix.diagonal (fun i => 1 - (Λ i)⁻¹) := by
                ext i j
                by_cases hij : i = j
                · subst hij; simp [Matrix.diagonal]
                · simp [Matrix.diagonal, hij]
              rw [hd]
    rw [heq]
    have hdiag_nn : (Matrix.diagonal (fun i => 1 - (Λ i)⁻¹)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (hΛge1 i))
    have h := hdiag_nn.mul_mul_conjTranspose_same U
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hBinv : B⁻¹ = S * C⁻¹ * S := by
    apply Matrix.inv_eq_right_inv
    have hB_eq : B = S⁻¹ * C * S⁻¹ := by
      calc
        B = (S⁻¹ * S) * B * (S * S⁻¹) := by
              rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_nonsing_inv S hSdet,
                Matrix.one_mul, Matrix.mul_one]
        _ = S⁻¹ * C * S⁻¹ := by
              rw [hC_def]
              simp only [Matrix.mul_assoc]
    have hCdet : IsUnit C.det := posDef_det_isUnit hC
    calc
      B * (S * C⁻¹ * S) = S⁻¹ * (C * (S⁻¹ * S) * C⁻¹) * S := by
            conv_lhs => rw [hB_eq]
            simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (C * C⁻¹) * S := by
            rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]
      _ = S⁻¹ * S := by
            rw [Matrix.mul_nonsing_inv C hCdet, Matrix.mul_one]
      _ = 1 := Matrix.nonsing_inv_mul S hSdet
  have hdiff : A⁻¹ - B⁻¹ = S * (1 - C⁻¹) * S := by
    rw [← hSS, hBinv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [hdiff]
  have h := hone_sub_Cinv.mul_mul_conjTranspose_same S
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hST] at h

/-- Coarse precision never exceeds the observation precision: `coarsePrecision A R Q ≤ R`. -/
theorem coarsePrecision_le_obsPrecision {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    (R - coarsePrecision A R Q).PosSemidef := by
  have hKinv : (finePrecision A R Q)⁻¹.PosDef := (finePrecision_posDef Q hA hR).inv
  have hRT : Rᵀ = R := posDef_transpose hR
  have hdiff : R - coarsePrecision A R Q = (R * Q) * (finePrecision A R Q)⁻¹ * (R * Q)ᵀ := by
    simp only [coarsePrecision, Matrix.transpose_mul, hRT,
      Matrix.conjTranspose_eq_transpose_of_trivial, sub_sub_cancel, Matrix.mul_assoc]
  rw [hdiff]
  have h := hKinv.posSemidef.mul_mul_conjTranspose_same (R * Q)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Fine precision after conditioning dominates the prior precision: `A ≤ finePrecision A R Q`. -/
theorem finePrecision_ge_priorPrecision {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (hR : R.PosDef) :
    (finePrecision A R Q - A).PosSemidef := by
  have hdiff : finePrecision A R Q - A = Qᴴ * R * Q := by
    simp only [finePrecision, add_sub_cancel_left]
  rw [hdiff]
  exact hR.posSemidef.conjTranspose_mul_mul_same Q

/-- Coarse covariance is antitone in the prior precision: `A₁ ≤ A₂ → Σ(A₂) ≤ Σ(A₁)`. -/
theorem coarseCovariance_antitone {n m : ℕ}
    {A₁ A₂ : Matrix (Fin n) (Fin n) ℝ} (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hle : (A₂ - A₁).PosSemidef) :
    (coarseCovariance A₁ R Q - coarseCovariance A₂ R Q).PosSemidef := by
  have hinv := posDef_inv_antitone hA₁ hA₂ hle
  have hdiff : coarseCovariance A₁ R Q - coarseCovariance A₂ R Q = Q * (A₁⁻¹ - A₂⁻¹) * Qᴴ := by
    simp only [coarseCovariance, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hdiff]
  exact hinv.mul_mul_conjTranspose_same Q

/-- Coarse precision is monotone in the prior precision: `A₁ ≤ A₂ → S(A₁) ≤ S(A₂)`. -/
theorem coarsePrecision_monotone {n m : ℕ}
    {A₁ A₂ : Matrix (Fin n) (Fin n) ℝ} (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR : R.PosDef) (hle : (A₂ - A₁).PosSemidef) :
    (coarsePrecision A₂ R Q - coarsePrecision A₁ R Q).PosSemidef := by
  rw [← coarseCovariance_inv Q hA₂ hR, ← coarseCovariance_inv Q hA₁ hR]
  exact posDef_inv_antitone (coarseCovariance_posDef Q hA₂ hR)
    (coarseCovariance_posDef Q hA₁ hR) (coarseCovariance_antitone R Q hA₁ hA₂ hle)

/-- **Schur Ratio Coupling Contraction**:
if `Qᵀ * R * Q ≤ c • A` with `0 ≤ c`, then
`Qᵀ * coarsePrecision A R Q * Q ≤ (c / (1 + c)) • A`. -/
theorem schur_pullback_le_ratio {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {c : ℝ} (hc : 0 ≤ c)
    (hbound : (c • A - Qᵀ * R * Q).PosSemidef) :
    ((c / (1 + c)) • A - Qᵀ * coarsePrecision A R Q * Q).PosSemidef := by
  have h1c : 0 < 1 + c := add_pos_of_pos_of_nonneg zero_lt_one hc
  have hK : (finePrecision A R Q).PosDef := finePrecision_posDef Q hA hR
  have hAdet : IsUnit A.det := posDef_det_isUnit hA
  have hAT : Aᵀ = A := posDef_transpose hA
  have h1cA : ((1 + c) • A).PosDef := hA.smul h1c
  have hK_le : ((1 + c) • A - finePrecision A R Q).PosSemidef := by
    have heq : (1 + c) • A - finePrecision A R Q = c • A - Qᵀ * R * Q := by
      simp only [finePrecision, Matrix.conjTranspose_eq_transpose_of_trivial, add_smul, one_smul]
      abel
    rw [heq]
    exact hbound
  have hinv_diff := posDef_inv_antitone hK h1cA hK_le
  have h1cAinv : ((1 + c) • A)⁻¹ = (1 + c)⁻¹ • A⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ h1c.ne', one_smul, Matrix.mul_nonsing_inv A hAdet]
  rw [h1cAinv] at hinv_diff
  have hA_Kinv_A : A * (finePrecision A R Q)⁻¹ * A = A - Qᵀ * coarsePrecision A R Q * Q := by
    have hfi := finePrecision_inv Q hA hR
    have heq : A * (finePrecision A R Q)⁻¹ * A =
        A * (A⁻¹ - A⁻¹ * Qᴴ * coarsePrecision A R Q * Q * A⁻¹) * A := by
      rw [hfi]
    rw [heq]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul]
    have h1 : A * A⁻¹ * A = A := by rw [Matrix.mul_nonsing_inv A hAdet, Matrix.one_mul]
    have h2 : A * (A⁻¹ * Qᵀ * coarsePrecision A R Q * Q * A⁻¹) * A =
        Qᵀ * coarsePrecision A R Q * Q := by
      calc
        A * (A⁻¹ * Qᵀ * coarsePrecision A R Q * Q * A⁻¹) * A
            = (A * A⁻¹) * (Qᵀ * coarsePrecision A R Q * Q) * (A⁻¹ * A) := by
              simp only [Matrix.mul_assoc]
        _ = Qᵀ * coarsePrecision A R Q * Q := by
              rw [Matrix.mul_nonsing_inv A hAdet, Matrix.nonsing_inv_mul A hAdet,
                Matrix.one_mul, Matrix.mul_one]
    rw [h1, h2]
  have hconj := hinv_diff.mul_mul_conjTranspose_same A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hAT,
    Matrix.mul_sub, Matrix.sub_mul, hA_Kinv_A,
    mul_smul_comm, smul_mul_assoc,
    Matrix.mul_nonsing_inv A hAdet, Matrix.one_mul] at hconj
  have hcoef : 1 - (1 + c)⁻¹ = c / (1 + c) := by
    field_simp [h1c.ne']
    ring
  have hgoal : (c / (1 + c)) • A - Qᵀ * coarsePrecision A R Q * Q =
      (A - Qᵀ * coarsePrecision A R Q * Q) - (1 + c)⁻¹ • A := by
    rw [← hcoef, sub_smul, one_smul]
    abel
  rw [hgoal]
  exact hconj

end SchurDeterminantAndLoewner

/-! ## Section 2: Fisher–Rao Coarse-Graining Information Loss & Contraction -/

section FisherRaoContraction

/-- Rectangular congruence pushforward of a symmetric tangent matrix `X ↦ Q X Qᵀ`. -/
def rectCongruence {n m : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Q * X * Qᵀ

@[simp] theorem rectCongruence_eq_congruenceAction {d : ℕ}
    (Q X : Matrix (Fin d) (Fin d) ℝ) :
    rectCongruence Q X = congruenceAction Q X :=
  rfl

theorem rectCongruence_transpose {n m : ℕ}
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (hX : Xᵀ = X) :
    (rectCongruence Q X)ᵀ = rectCongruence Q X := by
  dsimp [rectCongruence]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX, Matrix.mul_assoc]

/-- Exact sandwich identity relating conditioned fine covariance to the coarse pullback:
`A * (finePrecision A R Q)⁻¹ * A = A - Qᵀ * coarsePrecision A R Q * Q`. -/
theorem finePrecision_inv_sandwich {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (hA : A.PosDef) (hR : R.PosDef) :
    A * (finePrecision A R Q)⁻¹ * A = A - Qᵀ * coarsePrecision A R Q * Q := by
  have hAdet : IsUnit A.det := posDef_det_isUnit hA
  rw [finePrecision_inv Q hA hR]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul]
  have h1 : A * A⁻¹ * A = A := by rw [Matrix.mul_nonsing_inv A hAdet, Matrix.one_mul]
  have h2 : A * (A⁻¹ * Qᵀ * coarsePrecision A R Q * Q * A⁻¹) * A =
      Qᵀ * coarsePrecision A R Q * Q := by
    calc
      A * (A⁻¹ * Qᵀ * coarsePrecision A R Q * Q * A⁻¹) * A
          = (A * A⁻¹) * (Qᵀ * coarsePrecision A R Q * Q) * (A⁻¹ * A) := by
            simp only [Matrix.mul_assoc]
      _ = Qᵀ * coarsePrecision A R Q * Q := by
            rw [Matrix.mul_nonsing_inv A hAdet, Matrix.nonsing_inv_mul A hAdet,
              Matrix.one_mul, Matrix.mul_one]
  rw [h1, h2]

private theorem trace_quad_diff {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) :
    θ ^ 2 * (A * X * A * X).trace - (S * (Q * X * Qᵀ) * S * (Q * X * Qᵀ)).trace =
      θ * (A * (X * (θ • A - Qᵀ * S * Q) * X)).trace +
        ((Qᵀ * S * Q) * (X * (θ • A - Qᵀ * S * Q) * X)).trace := by
  set M := θ • A - Qᵀ * S * Q
  have hS : (S * (Q * X * Qᵀ) * S * (Q * X * Qᵀ)).trace =
      ((Qᵀ * S * Q) * X * (Qᵀ * S * Q) * X).trace := by
    have hcyc :
        (S * (Q * X * Qᵀ) * S * (Q * X * Qᵀ)).trace =
          (Qᵀ * (S * (Q * X * Qᵀ) * S * (Q * X))).trace := by
      have := Matrix.trace_mul_comm (S * (Q * X * Qᵀ) * S * (Q * X)) Qᵀ
      simpa only [Matrix.mul_assoc] using this
    rw [hcyc]
    simp only [Matrix.mul_assoc]
  have hcross : (A * (X * (Qᵀ * S * Q) * X)).trace = ((Qᵀ * S * Q) * (X * A * X)).trace := by
    calc
      (A * (X * (Qᵀ * S * Q) * X)).trace
          = ((A * X) * ((Qᵀ * S * Q) * X)).trace := by simp only [Matrix.mul_assoc]
      _ = (((Qᵀ * S * Q) * X) * (A * X)).trace := Matrix.trace_mul_comm _ _
      _ = ((Qᵀ * S * Q) * (X * A * X)).trace := by simp only [Matrix.mul_assoc]
  rw [hS]
  have hexp1 :
      θ * (A * (X * M * X)).trace =
        θ ^ 2 * (A * X * A * X).trace - θ * (A * (X * (Qᵀ * S * Q) * X)).trace := by
    dsimp [M]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
      mul_smul_comm, smul_mul_assoc, mul_smul_comm, Matrix.trace_smul]
    simp only [smul_eq_mul, Matrix.mul_assoc]
    ring
  have hexp2 :
      ((Qᵀ * S * Q) * (X * M * X)).trace =
        θ * ((Qᵀ * S * Q) * (X * A * X)).trace - ((Qᵀ * S * Q) * X * (Qᵀ * S * Q) * X).trace := by
    dsimp [M]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
      mul_smul_comm, smul_mul_assoc, mul_smul_comm, Matrix.trace_smul]
    simp only [smul_eq_mul, Matrix.mul_assoc]
  rw [hexp1, hexp2, hcross]
  ring

private theorem half_diff_eq {a b c d : ℝ} (h : a - b = c + d) :
    (1 / 2 : ℝ) * a - (1 / 2 : ℝ) * b = (1 / 2 : ℝ) * c + (1 / 2 : ℝ) * d := by
  rw [← mul_sub, h, mul_add]

private theorem half_scaled_le {θ a b c d : ℝ} (h : θ ^ 2 * a - b = c + d)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (1 / 2 : ℝ) * b ≤ θ ^ 2 * ((1 / 2 : ℝ) * a) := by
  have h1 : 0 ≤ (1 / 2 : ℝ) * (θ ^ 2 * a - b) := by
    rw [h]
    exact mul_nonneg (by norm_num) (add_nonneg hc hd)
  rw [mul_sub, mul_left_comm (1 / 2 : ℝ) (θ ^ 2) a] at h1
  exact sub_nonneg.mp h1

/-- **Exact Fisher–Rao Coarse-Graining Information-Loss Identity**:
the Fisher–Rao metric difference equals a sum of two nonnegative traces governed by
`Δ_Schur = A * K⁻¹ * A = A - Qᵀ S Q`. -/
theorem fisherRao_coarseGraining_defect_eq {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    fisherRaoMetric A X X -
        fisherRaoMetric (coarsePrecision A R Q) (rectCongruence Q X) (rectCongruence Q X) =
      (1 / 2 : ℝ) * (A * (X * (A * (finePrecision A R Q)⁻¹ * A) * X)).trace +
        (1 / 2 : ℝ) *
          (Qᵀ * coarsePrecision A R Q * Q * (X * (A * (finePrecision A R Q)⁻¹ * A) * X)).trace := by
  dsimp [fisherRaoMetric, rectCongruence]
  rw [finePrecision_inv_sandwich A R Q hA hR]
  have hq := trace_quad_diff A (coarsePrecision A R Q) Q X 1
  simp only [one_pow, one_mul, one_smul] at hq
  exact half_diff_eq hq

/-- **Fisher–Rao Coarse-Graining Monotonicity (Data Processing)**:
for any positive-definite precisions `A`, `R` and arbitrary rectangular coarse-graining `Q`,
the coarse Fisher–Rao norm is never larger than the fine Fisher–Rao norm. -/
theorem fisherRao_coarseGraining_le {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hX : Xᵀ = X) :
    fisherRaoMetric (coarsePrecision A R Q) (rectCongruence Q X) (rectCongruence Q X) ≤
      fisherRaoMetric A X X := by
  have hAT : Aᵀ = A := posDef_transpose hA
  have hKinv_A : (A * (finePrecision A R Q)⁻¹ * A).PosDef := by
    have hKinv : (finePrecision A R Q)⁻¹.PosDef := (finePrecision_posDef Q hA hR).inv
    have h := hKinv.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hA.isUnit)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hAT] at h
  have hXMX : (X * (A * (finePrecision A R Q)⁻¹ * A) * X).PosSemidef := by
    have h := hKinv_A.posSemidef.mul_mul_conjTranspose_same X
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hX] at h
  have hQSQ : (Qᵀ * coarsePrecision A R Q * Q).PosSemidef := by
    have h := (coarsePrecision_posDef Q hA hR).posSemidef.conjTranspose_mul_mul_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have ht1 : 0 ≤ (A * (X * (A * (finePrecision A R Q)⁻¹ * A) * X)).trace :=
    trace_posSemidef_mul_posSemidef_nonneg hA.posSemidef hXMX
  have ht2 : 0 ≤ (Qᵀ * coarsePrecision A R Q * Q * (X * (A * (finePrecision A R Q)⁻¹ * A) * X)).trace :=
    trace_posSemidef_mul_posSemidef_nonneg hQSQ hXMX
  have hdef := fisherRao_coarseGraining_defect_eq A R Q X hA hR
  exact sub_nonneg.mp (by
    rw [hdef]
    exact add_nonneg (mul_nonneg (by norm_num) ht1) (mul_nonneg (by norm_num) ht2))

/-- **Strict Fisher–Rao Contraction**:
whenever `R` and `A` are positive definite and `X ≠ 0` is symmetric, coarse-graining
strictly decreases the Fisher–Rao information norm (`g_S(Q X Qᵀ) < g_A(X)`). -/
theorem fisherRao_coarseGraining_strict_lt {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hX : Xᵀ = X) (hXne : X ≠ 0) :
    fisherRaoMetric (coarsePrecision A R Q) (rectCongruence Q X) (rectCongruence Q X) <
      fisherRaoMetric A X X := by
  have hAT : Aᵀ = A := posDef_transpose hA
  have hKinv_A : (A * (finePrecision A R Q)⁻¹ * A).PosDef := by
    have hKinv : (finePrecision A R Q)⁻¹.PosDef := (finePrecision_posDef Q hA hR).inv
    have h := hKinv.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hA.isUnit)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hAT] at h
  have hXMX : (X * (A * (finePrecision A R Q)⁻¹ * A) * X).PosSemidef := by
    have h := hKinv_A.posSemidef.mul_mul_conjTranspose_same X
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hX] at h
  have hXMX_ne : X * (A * (finePrecision A R Q)⁻¹ * A) * X ≠ 0 := by
    intro hz
    have hzero : ∃ i, X *ᵥ Pi.single i 1 ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hXne
      ext i j
      have hcol := congrFun (hnone j) i
      change (X *ᵥ Pi.single j 1) i = (0 : Fin n → ℝ) i at hcol
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at hcol
      exact hcol
    rcases hzero with ⟨j, hj⟩
    have hval := congrArg (fun M => Pi.single j (1 : ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1)) hz
    have heq :
        Pi.single j (1 : ℝ) ⬝ᵥ ((X * (A * (finePrecision A R Q)⁻¹ * A) * X) *ᵥ Pi.single j 1) =
          (X *ᵥ Pi.single j 1) ⬝ᵥ ((A * (finePrecision A R Q)⁻¹ * A) *ᵥ (X *ᵥ Pi.single j 1)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      congr 1
      nth_rw 1 [← hX]
      rw [Matrix.vecMul_transpose]
    rw [heq, Matrix.zero_mulVec, dotProduct_zero] at hval
    have hpos := hKinv_A.re_dotProduct_pos hj
    simp only [RCLike.re_to_real, star_trivial] at hpos
    exact hpos.ne' hval
  have ht1_pos : 0 < (A * (X * (A * (finePrecision A R Q)⁻¹ * A) * X)).trace := by
    have hnn := trace_posSemidef_mul_posSemidef_nonneg hA.posSemidef hXMX
    refine lt_of_le_of_ne hnn ?_
    intro h0
    exact hXMX_ne ((trace_posDef_mul_posSemidef_eq_zero_iff hA hXMX).mp h0.symm)
  have hQSQ : (Qᵀ * coarsePrecision A R Q * Q).PosSemidef := by
    have h := (coarsePrecision_posDef Q hA hR).posSemidef.conjTranspose_mul_mul_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have ht2 : 0 ≤ (Qᵀ * coarsePrecision A R Q * Q * (X * (A * (finePrecision A R Q)⁻¹ * A) * X)).trace :=
    trace_posSemidef_mul_posSemidef_nonneg hQSQ hXMX
  have hdef := fisherRao_coarseGraining_defect_eq A R Q X hA hR
  exact sub_pos.mp (by
    rw [hdef]
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) ht1_pos)
      (mul_nonneg (by norm_num) ht2))

/-- **Quantitative Fisher–Rao Contraction from a Pullback Loewner Bound**:
if `0 ≤ θ` and `Qᵀ S Q ≤ θ • A`, then `g_S(Q X Qᵀ) ≤ θ ^ 2 * g_A(X)`. -/
theorem fisherRao_coarseGraining_contraction_of_le_ratio {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hX : Xᵀ = X) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : (θ • A - Qᵀ * coarsePrecision A R Q * Q).PosSemidef) :
    fisherRaoMetric (coarsePrecision A R Q) (rectCongruence Q X) (rectCongruence Q X) ≤
      θ ^ 2 * fisherRaoMetric A X X := by
  have hXMX : (X * (θ • A - Qᵀ * coarsePrecision A R Q * Q) * X).PosSemidef := by
    have h := hbound.mul_mul_conjTranspose_same X
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hX] at h
  have hQSQ : (Qᵀ * coarsePrecision A R Q * Q).PosSemidef := by
    have h := (coarsePrecision_posDef Q hA hR).posSemidef.conjTranspose_mul_mul_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have ht1 : 0 ≤ θ * (A * (X * (θ • A - Qᵀ * coarsePrecision A R Q * Q) * X)).trace :=
    mul_nonneg hθ (trace_posSemidef_mul_posSemidef_nonneg hA.posSemidef hXMX)
  have ht2 :
      0 ≤ ((Qᵀ * coarsePrecision A R Q * Q) *
        (X * (θ • A - Qᵀ * coarsePrecision A R Q * Q) * X)).trace :=
    trace_posSemidef_mul_posSemidef_nonneg hQSQ hXMX
  have hq := trace_quad_diff A (coarsePrecision A R Q) Q X θ
  dsimp [fisherRaoMetric, rectCongruence]
  exact half_scaled_le hq ht1 ht2

/-- **Quantitative Wilson–Gaussian Fisher Contraction**:
if `0 ≤ c` and `Qᵀ R Q ≤ c • A`, then
`g_S(Q X Qᵀ) ≤ (c / (1 + c)) ^ 2 * g_A(X)`. -/
theorem fisherRao_coarseGraining_contraction_of_coupling_bound {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hX : Xᵀ = X) {c : ℝ} (hc : 0 ≤ c)
    (hbound : (c • A - Qᵀ * R * Q).PosSemidef) :
    fisherRaoMetric (coarsePrecision A R Q) (rectCongruence Q X) (rectCongruence Q X) ≤
      (c / (1 + c)) ^ 2 * fisherRaoMetric A X X :=
  fisherRao_coarseGraining_contraction_of_le_ratio A R Q X hA hR hX
    (div_nonneg hc (add_pos_of_pos_of_nonneg zero_lt_one hc).le)
    (schur_pullback_le_ratio A R Q hA hR hc hbound)

end FisherRaoContraction

/-! ## Section 3: Multivariate Gaussian Block-Spin Pushforward & KL Data Processing -/

section MultivariateGaussianKL

/-- Continuous linear map induced by an arbitrary rectangular real matrix
`Q : Matrix (Fin m) (Fin n) ℝ` between `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`. -/
def rectEuclideanCLM {n m : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q)

@[simp] theorem ofLp_rectEuclideanCLM {n m : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (rectEuclideanCLM Q x) = Q *ᵥ WithLp.ofLp x :=
  rfl

theorem inner_rectEuclideanCLM {n m : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪y, rectEuclideanCLM Q x⟫ = WithLp.ofLp y ⬝ᵥ (Q *ᵥ WithLp.ofLp x) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ofLp_rectEuclideanCLM, dotProduct]
  congr 1 with i
  exact mul_comm _ _

theorem adjoint_rectEuclideanCLM {n m : ℕ} (Q : Matrix (Fin m) (Fin n) ℝ) :
    ContinuousLinearMap.adjoint (rectEuclideanCLM Q) = rectEuclideanCLM Qᵀ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_rectEuclideanCLM, real_inner_comm, inner_rectEuclideanCLM,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

/-- **Rectangular Linear Pushforward of a Centered Multivariate Gaussian**:
`(𝒩(0, S)).map Q = 𝒩(0, Q S Qᵀ)`. -/
theorem map_multivariateGaussian_rect_clm {n m : ℕ}
    (Q : Matrix (Fin m) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map (rectEuclideanCLM Q) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (Q * S * Qᵀ) := by
  have hQSQT : (Q * S * Qᵀ).PosSemidef := by
    have h := hS.mul_mul_conjTranspose_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have algiden : ∀ (u v : Fin m → ℝ),
      (Qᵀ *ᵥ u) ⬝ᵥ (S *ᵥ (Qᵀ *ᵥ v)) = u ⬝ᵥ ((Q * S * Qᵀ) *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc]
  refine IsGaussian.ext ?_ ?_
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian, map_zero]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id (rectEuclideanCLM Q) u v,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hQSQT,
      adjoint_rectEuclideanCLM]
    simp only [ofLp_rectEuclideanCLM]
    exact algiden _ _

/-- **Gaussian Convolution Law**:
`𝒩(0, S₁) ∗ 𝒩(0, S₂) = 𝒩(0, S₁ + S₂)` without commutation assumptions. -/
theorem multivariateGaussian_conv_multivariateGaussian {m : ℕ}
    (S₁ S₂ : Matrix (Fin m) (Fin m) ℝ)
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S₁) ∗
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S₂) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (S₁ + S₂) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hS₁,
    charFun_multivariateGaussian hS₂, charFun_multivariateGaussian (hS₁.add hS₂),
    ← Complex.exp_add]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, Matrix.add_mulVec, dotProduct_add,
    Complex.ofReal_add]
  ring

/-- **Wilson Block-Spin Covariance Soldering**:
pushing forward `𝒩(0, A⁻¹)` by `Q` and convolving with coarse observation noise
`𝒩(0, R⁻¹)` equals `𝒩(0, coarseCovariance A R Q)`. -/
theorem wilsonGaussianBlockSpin_measure_eq {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (hA : A.PosDef) (hR : R.PosDef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A⁻¹).map (rectEuclideanCLM Q)) ∗
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A R Q) := by
  rw [map_multivariateGaussian_rect_clm Q A⁻¹ hA.inv.posSemidef]
  have hQAT : (Q * A⁻¹ * Qᵀ).PosSemidef := by
    have h := hA.inv.posSemidef.mul_mul_conjTranspose_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [multivariateGaussian_conv_multivariateGaussian _ _ hQAT hR.inv.posSemidef, add_comm]
  simp only [coarseCovariance, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Wilson–Gaussian KL Data-Processing Inequality**:
for arbitrary SPD priors `A₁, A₂`, noise `R`, and rectangular observation `Q`,
`D_KL(𝒩(0, coarseCovariance A₁ R Q) ‖ 𝒩(0, coarseCovariance A₂ R Q)) ≤ D_KL(𝒩(0, A₁⁻¹) ‖ 𝒩(0, A₂⁻¹))`. -/
theorem klDiv_coarseCovariance_le {n m : ℕ}
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR : R.PosDef) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A₁ R Q))
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A₂ R Q)) ≤
      klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹)
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹) := by
  rw [← wilsonGaussianBlockSpin_measure_eq A₁ R Q hA₁ hR,
    ← wilsonGaussianBlockSpin_measure_eq A₂ R Q hA₂ hR]
  have hadd :
      klDiv
          (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹).map (rectEuclideanCLM Q)).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹) |>.map
              (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => p.1 + p.2))
          (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹).map (rectEuclideanCLM Q)).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹) |>.map
              (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => p.1 + p.2)) ≤
        klDiv
          (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹).map (rectEuclideanCLM Q)).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹))
          (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹).map (rectEuclideanCLM Q)).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹)) :=
    InformationTheory.klDiv_map_le _ _ measurable_add
  calc
    klDiv
        (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹).map (rectEuclideanCLM Q)) ∗
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹))
        (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹).map (rectEuclideanCLM Q)) ∗
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹))
        ≤ klDiv
            (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹).map (rectEuclideanCLM Q)).prod
              (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹))
            (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹).map (rectEuclideanCLM Q)).prod
              (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹)) := hadd
    _ = klDiv
          ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹).map (rectEuclideanCLM Q))
          ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹).map (rectEuclideanCLM Q)) +
        klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹)
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R⁻¹) :=
        klDiv_prod_eq_add _ _ _ _
    _ = klDiv
          ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹).map (rectEuclideanCLM Q))
          ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹).map (rectEuclideanCLM Q)) := by
        rw [klDiv_self, add_zero]
    _ ≤ klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹)
              (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹) :=
        InformationTheory.klDiv_map_le _ _ (rectEuclideanCLM Q).continuous.measurable

/-- Real-valued `toReal` KL monotonicity under Wilson–Gaussian coarse-graining. -/
theorem toReal_klDiv_coarseCovariance_le {n m : ℕ}
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR : R.PosDef) :
    (klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A₁ R Q))
           (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A₂ R Q))).toReal ≤
      (klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₁⁻¹)
             (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) A₂⁻¹)).toReal :=
  ENNReal.toReal_mono (klDiv_multivariateGaussian_zero_ne_top A₁⁻¹ A₂⁻¹ hA₁.inv hA₂.inv)
    (klDiv_coarseCovariance_le A₁ A₂ R Q hA₁ hA₂ hR)

/-- **Trace–Logdet Schur Contraction**:
direct algebraic corollary via `GaussianTraceLogdet` comparing fine and coarse precision
relative entropies `(S₂⁻¹ = Σ₂, S₁⁻¹ = Σ₁)` without commutation. -/
theorem trace_logdet_coarseCovariance_le {n m : ℕ}
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR : R.PosDef) :
    Real.log (coarseCovariance A₂ R Q).det - Real.log (coarseCovariance A₁ R Q).det +
        (coarsePrecision A₂ R Q * coarseCovariance A₁ R Q).trace - m ≤
      Real.log A₂⁻¹.det - Real.log A₁⁻¹.det + (A₂ * A₁⁻¹).trace - n := by
  have hle := toReal_klDiv_coarseCovariance_le A₁ A₂ R Q hA₁ hA₂ hR
  rw [toReal_klDiv_multivariateGaussian_zero (coarseCovariance A₁ R Q) (coarseCovariance A₂ R Q)
      (coarseCovariance_posDef Q hA₁ hR) (coarseCovariance_posDef Q hA₂ hR),
    toReal_klDiv_multivariateGaussian_zero A₁⁻¹ A₂⁻¹ hA₁.inv hA₂.inv,
    coarseCovariance_inv Q hA₂ hR] at hle
  have hinv2 : (A₂⁻¹)⁻¹ = A₂ := by
    letI := hA₂.isUnit.invertible
    exact Matrix.inv_inv_of_invertible A₂
  rw [hinv2] at hle
  exact le_of_mul_le_mul_left hle (by norm_num : (0 : ℝ) < 2⁻¹)

private theorem coarsePrecision_inv_eq_coarseCovariance {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin m) (Fin n) ℝ) (hA : A.PosDef) (hR : R.PosDef) :
    (coarsePrecision A R Q)⁻¹ = coarseCovariance A R Q :=
  coarsePrecision_inv Q hA hR

end MultivariateGaussianKL

/-! ## Section 4: Two-Step Composition & Multi-Step Iterated RG Contraction Tower -/

section IteratedRGTower

/-- **Two-Stage Rectangular KL Data-Processing Contraction**:
welds `CoarseGrainingComposition.twoStage_coarsePrecision_inv` with KL monotonicity. -/
theorem twoStage_klDiv_contraction {n m l : ℕ}
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ)
    (R₁ : Matrix (Fin m) (Fin m) ℝ) (R₂ : Matrix (Fin l) (Fin l) ℝ)
    (Q₁ : Matrix (Fin m) (Fin n) ℝ) (Q₂ : Matrix (Fin l) (Fin m) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) :
    let S₁ := coarsePrecision A₁ R₁ Q₁
    let S₂ := coarsePrecision A₂ R₁ Q₁
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin l)) (coarseCovariance S₁ R₂ Q₂))
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin l)) (coarseCovariance S₂ R₂ Q₂)) ≤
      klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A₁ R₁ Q₁))
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (coarseCovariance A₂ R₁ Q₁)) := by
  dsimp only
  have hS₁ := coarsePrecision_posDef Q₁ hA₁ hR₁
  have hS₂ := coarsePrecision_posDef Q₁ hA₂ hR₁
  have h2 := klDiv_coarseCovariance_le (coarsePrecision A₁ R₁ Q₁) (coarsePrecision A₂ R₁ Q₁) R₂ Q₂
    hS₁ hS₂ hR₂
  rw [coarsePrecision_inv_eq_coarseCovariance A₁ R₁ Q₁ hA₁ hR₁,
    coarsePrecision_inv_eq_coarseCovariance A₂ R₁ Q₁ hA₂ hR₁] at h2
  exact h2

/-- **Two-Stage Rectangular Fisher–Rao Contraction**:
chains `rectCongruence` across arbitrary rectangular transitions `Fin n → Fin m → Fin l`. -/
theorem twoStage_fisherRao_contraction {n m l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (R₁ : Matrix (Fin m) (Fin m) ℝ) (R₂ : Matrix (Fin l) (Fin l) ℝ)
    (Q₁ : Matrix (Fin m) (Fin n) ℝ) (Q₂ : Matrix (Fin l) (Fin m) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) (hX : Xᵀ = X) :
    let S₁ := coarsePrecision A R₁ Q₁
    let S₂ := coarsePrecision S₁ R₂ Q₂
    fisherRaoMetric S₂ (rectCongruence (Q₂ * Q₁) X) (rectCongruence (Q₂ * Q₁) X) ≤
      fisherRaoMetric S₁ (rectCongruence Q₁ X) (rectCongruence Q₁ X) ∧
    fisherRaoMetric S₁ (rectCongruence Q₁ X) (rectCongruence Q₁ X) ≤
      fisherRaoMetric A X X := by
  dsimp only
  have hS₁ := coarsePrecision_posDef Q₁ hA hR₁
  have hQX := rectCongruence_transpose Q₁ X hX
  have hcomp : rectCongruence (Q₂ * Q₁) X = rectCongruence Q₂ (rectCongruence Q₁ X) := by
    simp only [rectCongruence, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hcomp]
  exact ⟨fisherRao_coarseGraining_le (coarsePrecision A R₁ Q₁) R₂ Q₂ (rectCongruence Q₁ X)
      hS₁ hR₂ hQX,
    fisherRao_coarseGraining_le A R₁ Q₁ X hA hR₁ hX⟩

/-- `k`-step iterated Wilson–Gaussian coarse precision on `Fin d`. -/
def rgIterPrecision {d : ℕ}
    (R Q : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ
  | 0, A => A
  | k + 1, A => coarsePrecision (rgIterPrecision R Q k A) R Q

/-- `k`-step iterated congruence tangent on `Fin d`. -/
def rgIterTangent {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ
  | 0, X => X
  | k + 1, X => rectCongruence Q (rgIterTangent Q k X)

theorem rgIterPrecision_posDef {d : ℕ}
    (R Q : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosDef) :
    ∀ k (A : Matrix (Fin d) (Fin d) ℝ), A.PosDef → (rgIterPrecision R Q k A).PosDef
  | 0, _, hA => hA
  | k + 1, A, hA => coarsePrecision_posDef Q (rgIterPrecision_posDef R Q hR k A hA) hR

theorem rgIterTangent_transpose {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) :
    ∀ k (X : Matrix (Fin d) (Fin d) ℝ), Xᵀ = X → (rgIterTangent Q k X)ᵀ = rgIterTangent Q k X
  | 0, _, hX => hX
  | k + 1, X, hX => rectCongruence_transpose Q _ (rgIterTangent_transpose Q k X hX)

/-- **Iterated RG Tower KL Monotonicity**:
the centered Gaussian KL divergence along the `k`-step Wilson–Gaussian RG flow is antitone in `k`. -/
theorem rgIter_klDiv_antitone {d : ℕ}
    (A₁ A₂ R Q : Matrix (Fin d) (Fin d) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR : R.PosDef) :
    Antitone fun k : ℕ =>
      klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (rgIterPrecision R Q k A₁)⁻¹)
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (rgIterPrecision R Q k A₂)⁻¹) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h1 := rgIterPrecision_posDef R Q hR k A₁ hA₁
  have h2 := rgIterPrecision_posDef R Q hR k A₂ hA₂
  have hle := klDiv_coarseCovariance_le (rgIterPrecision R Q k A₁) (rgIterPrecision R Q k A₂)
    R Q h1 h2 hR
  change klDiv (multivariateGaussian 0 (coarsePrecision (rgIterPrecision R Q k A₁) R Q)⁻¹)
        (multivariateGaussian 0 (coarsePrecision (rgIterPrecision R Q k A₂) R Q)⁻¹) ≤
      klDiv (multivariateGaussian 0 (rgIterPrecision R Q k A₁)⁻¹)
        (multivariateGaussian 0 (rgIterPrecision R Q k A₂)⁻¹)
  rwa [coarsePrecision_inv Q h1 hR, coarsePrecision_inv Q h2 hR]

/-- **Iterated RG Tower Fisher–Rao Monotonicity**:
the Fisher–Rao norm of pushed-forward tangents along the `k`-step RG flow is antitone in `k`. -/
theorem rgIter_fisherRao_antitone {d : ℕ}
    (A R Q X : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hX : Xᵀ = X) :
    Antitone fun k : ℕ =>
      fisherRaoMetric (rgIterPrecision R Q k A) (rgIterTangent Q k X) (rgIterTangent Q k X) := by
  refine antitone_nat_of_succ_le fun k => ?_
  exact fisherRao_coarseGraining_le (rgIterPrecision R Q k A) R Q (rgIterTangent Q k X)
    (rgIterPrecision_posDef R Q hR k A hA) hR (rgIterTangent_transpose Q k X hX)

/-- **Multi-Step Quantitative Geometric RG Contraction**:
under uniform step-wise coupling bound `Qᵀ R Q ≤ c A_j` for all `j < k`,
`g_{A_k}(X_k, X_k) ≤ (c / (1 + c)) ^ (2 * k) * g_A(X, X)`. -/
theorem rgIter_fisherRao_geometric_decay {d : ℕ}
    (A R Q X : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hX : Xᵀ = X) {c : ℝ} (hc : 0 ≤ c) :
    ∀ k : ℕ,
      (∀ j : ℕ, j < k → (c • rgIterPrecision R Q j A - Qᵀ * R * Q).PosSemidef) →
      fisherRaoMetric (rgIterPrecision R Q k A) (rgIterTangent Q k X) (rgIterTangent Q k X) ≤
        (c / (1 + c)) ^ (2 * k) * fisherRaoMetric A X X
  | 0, _ => by simp [rgIterPrecision, rgIterTangent]
  | k + 1, hbound => by
    have hk_bound : ∀ j : ℕ, j < k →
        (c • rgIterPrecision R Q j A - Qᵀ * R * Q).PosSemidef :=
      fun j hj => hbound j (Nat.lt_succ_of_lt hj)
    have ih := rgIter_fisherRao_geometric_decay A R Q X hA hR hX hc k hk_bound
    have hstep := fisherRao_coarseGraining_contraction_of_coupling_bound
      (rgIterPrecision R Q k A) R Q (rgIterTangent Q k X)
      (rgIterPrecision_posDef R Q hR k A hA) hR (rgIterTangent_transpose Q k X hX) hc
      (hbound k (Nat.lt_succ_self k))
    have hrate : 0 ≤ (c / (1 + c)) ^ 2 := sq_nonneg _
    have hmul := le_trans hstep (mul_le_mul_of_nonneg_left ih hrate)
    have hpow : (c / (1 + c)) ^ 2 * (c / (1 + c)) ^ (2 * k) =
        (c / (1 + c)) ^ (2 * (k + 1)) := by
      rw [← pow_add, show 2 + 2 * k = 2 * (k + 1) by omega]
    simpa only [rgIterPrecision, rgIterTangent, ← mul_assoc, hpow] using hmul

end IteratedRGTower

/-! ## Section 5: Peirce / Causal Pinching Specialization -/

section CausalPinchingSpecialization

/-- For any symmetric causal projector `P` (`P * P = P ∧ Pᵀ = P`), rectangular congruence
coincides identically with `PetzDataProcessingMonotonicity.causalChannel P`. -/
@[simp] theorem rectCongruence_eq_causalChannel {d : ℕ}
    (P X : Matrix (Fin d) (Fin d) ℝ) (hP : isCausalProjector P) :
    rectCongruence P X = causalChannel P X := by
  dsimp [rectCongruence, causalChannel]
  rw [hP.2]

/-- Covariance under causal pinching noise:
`coarseCovariance A R P = R⁻¹ + causalChannel P A⁻¹`. -/
theorem coarseCovariance_causalProjector_eq {d : ℕ}
    (A R P : Matrix (Fin d) (Fin d) ℝ) (hP : isCausalProjector P) :
    coarseCovariance A R P = R⁻¹ + causalChannel P A⁻¹ := by
  dsimp [coarseCovariance, causalChannel]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hP.2]

/-- Fisher–Rao contraction for a causal pinching channel `causalChannel P`. -/
theorem fisherRao_causalChannel_coarseGraining_le {d : ℕ}
    (A R P X : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hP : isCausalProjector P) (hX : Xᵀ = X) :
    fisherRaoMetric (coarsePrecision A R P) (causalChannel P X) (causalChannel P X) ≤
      fisherRaoMetric A X X := by
  rw [← rectCongruence_eq_causalChannel P X hP]
  exact fisherRao_coarseGraining_le A R P X hA hR hX

/-- Strict Fisher–Rao contraction for a causal pinching channel whenever `X ≠ 0`. -/
theorem fisherRao_causalChannel_coarseGraining_strict_lt {d : ℕ}
    (A R P X : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (hP : isCausalProjector P) (hX : Xᵀ = X) (hXne : X ≠ 0) :
    fisherRaoMetric (coarsePrecision A R P) (causalChannel P X) (causalChannel P X) <
      fisherRaoMetric A X X := by
  rw [← rectCongruence_eq_causalChannel P X hP]
  exact fisherRao_coarseGraining_strict_lt A R P X hA hR hX hXne

/-- KL data-processing inequality under causal pinching + coarse noise `R⁻¹`. -/
theorem klDiv_causalChannel_coarseCovariance_le {d : ℕ}
    (A₁ A₂ R P : Matrix (Fin d) (Fin d) ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hR : R.PosDef) (hP : isCausalProjector P) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (R⁻¹ + causalChannel P A₁⁻¹))
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (R⁻¹ + causalChannel P A₂⁻¹)) ≤
      klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A₁⁻¹)
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A₂⁻¹) := by
  rw [← coarseCovariance_causalProjector_eq A₁ R P hP,
    ← coarseCovariance_causalProjector_eq A₂ R P hP]
  exact klDiv_coarseCovariance_le A₁ A₂ R P hA₁ hA₂ hR

end CausalPinchingSpecialization

end InfoGeometry.Canonical.SchurCoarseGrainingFisherRGBridge
