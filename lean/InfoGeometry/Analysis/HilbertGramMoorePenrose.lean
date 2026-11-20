/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.HilbertGramReciprocity
import InfoGeometry.Singular.MoorePenrose

/-!
# Moore--Penrose action on Gram eigenspaces and a closed-range obstruction

For a bounded Moore--Penrose pair `A : E →L[𝕜] F`, `B : F →L[𝕜] E`,
the inverse `B` acts on the nonzero eigenspace of `A ∘L A.adjoint` with
eigenvalue `μ` as `μ⁻¹ • A.adjoint`. On a positive real eigenspace this agrees
with the inverse of the normalized Gram isometry up to multiplication by
the square root of the eigenvalue.

The resulting norm law gives `1 ≤ r * ‖B‖ ^ 2` for each actual positive
Gram eigenvalue `r`. Thus arbitrarily small actual positive eigenvalues
prevent the range of `A` from being closed: a closed range would supply the
existing bounded Moore--Penrose construction and contradict that norm bound.

The ambient Hilbert spaces may have different or infinite dimensions. The
argument uses point-spectrum witnesses, without a spectral-completeness,
compactness, finite-rank, trace-class, or unbounded-operator assumption.
-/

noncomputable section

namespace InfoGeometry.Analysis.HilbertGramMoorePenrose

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Analysis.HilbertGramReciprocity

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The inner-inverse identity and self-adjointness of `B ∘L A` already
suffice to show that this source projection fixes the adjoint of `A`.
The other two Moore--Penrose identities are not required for this step. -/
theorem comp_adjoint_eq_of_inner_inverse
    (A : E →L[𝕜] F) (B : F →L[𝕜] E)
    (hABA : (A.comp B).comp A = A)
    (hBA : (B.comp A).adjoint = B.comp A) :
    (B.comp A).comp A.adjoint = A.adjoint := by
  have hBA' : A.adjoint.comp B.adjoint = B.comp A := by
    simpa only [ContinuousLinearMap.adjoint_comp] using hBA
  have hadj := congrArg (fun T : E →L[𝕜] F => T.adjoint) hABA
  simp only [ContinuousLinearMap.adjoint_comp] at hadj
  rw [← ContinuousLinearMap.comp_assoc, hBA'] at hadj
  exact hadj

/-- On a native nonzero target Gram eigenspace, a Moore--Penrose inverse
is the inverse-eigenvalue multiple of the adjoint. The vector may be zero;
only the eigenvalue must be nonzero. -/
theorem apply_eq_inv_smul_adjoint_of_mem_eigenspace
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (hMP : IsMoorePenroseInverseCLM A B)
    {μ : 𝕜} (hμ : μ ≠ 0) {y : F}
    (hy : y ∈ Module.End.eigenspace (A.comp A.adjoint).toLinearMap μ) :
    B y = μ⁻¹ • A.adjoint y := by
  have hBA : (B.comp A).adjoint = B.comp A := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hMP.2.2.2
  have hfix := comp_adjoint_eq_of_inner_inverse A B hMP.1 hBA
  have heigen : A (A.adjoint y) = μ • y := Module.End.mem_eigenspace_iff.mp hy
  have hfix_y : B (A (A.adjoint y)) = A.adjoint y := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : F →L[𝕜] E => T y) hfix
  rw [heigen, map_smul] at hfix_y
  calc
    B y = μ⁻¹ • (μ • B y) := by
      rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • A.adjoint y := by rw [hfix_y]

/-- The eigenspace formula applies to the existing bounded Moore--Penrose
construction under its explicit closed-range hypothesis. -/
theorem moorePenroseInverse_apply_of_mem_eigenspace
    (A : E →L[𝕜] F) (hClosed : IsClosed (A.range : Set F))
    {μ : 𝕜} (hμ : μ ≠ 0) {y : F}
    (hy : y ∈ Module.End.eigenspace (A.comp A.adjoint).toLinearMap μ) :
    moorePenroseInverse A hClosed y = μ⁻¹ • A.adjoint y :=
  apply_eq_inv_smul_adjoint_of_mem_eigenspace A (moorePenroseInverse A hClosed)
    (isMoorePenroseInverse_moorePenroseInverse A hClosed) hμ hy

/-- The inverse of the normalized Gram isometry equals the square-root
multiple of the Moore--Penrose operator on the same native eigenspace. -/
theorem normalized_symm_eq_sqrt_smul
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (hMP : IsMoorePenroseInverseCLM A B)
    (r : ℝ) (hr : 0 < r)
    (y : Module.End.eigenspace (A.comp A.adjoint).toLinearMap (r : 𝕜)) :
    ((normalizedGramEigenspaceEquiv A r hr).symm y : E) =
      (Real.sqrt r : 𝕜) • B (y : F) := by
  rw [normalizedGramEigenspaceEquiv_symm_apply,
    apply_eq_inv_smul_adjoint_of_mem_eigenspace A B hMP
      (RCLike.ofReal_ne_zero.mpr hr.ne') y.property,
    smul_smul]
  congr 1
  have hsqrt : (Real.sqrt r : 𝕜) ^ 2 = (r : 𝕜) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have hsqrt_ne : (Real.sqrt r : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  simp only [RCLike.ofReal_inv]
  rw [← hsqrt]
  field_simp [hsqrt_ne]

/-- Exact norm scaling of a Moore--Penrose inverse on a positive Gram
eigenspace, obtained from the actual normalized linear isometry. -/
theorem norm_apply_of_mem_eigenspace
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (hMP : IsMoorePenroseInverseCLM A B)
    (r : ℝ) (hr : 0 < r) {y : F}
    (hy : y ∈ Module.End.eigenspace (A.comp A.adjoint).toLinearMap (r : 𝕜)) :
    ‖B y‖ = ‖y‖ / Real.sqrt r := by
  let y' : Module.End.eigenspace (A.comp A.adjoint).toLinearMap (r : 𝕜) := ⟨y, hy⟩
  have hnorm : ‖((normalizedGramEigenspaceEquiv A r hr).symm y' : E)‖ = ‖y‖ :=
    (normalizedGramEigenspaceEquiv A r hr).symm.norm_map y'
  rw [normalized_symm_eq_sqrt_smul A B hMP r hr y', norm_smul,
    RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg r)] at hnorm
  change Real.sqrt r * ‖B y‖ = ‖y‖ at hnorm
  apply (eq_div_iff (Real.sqrt_pos.mpr hr).ne').2
  exact (mul_comm ‖B y‖ (Real.sqrt r)).trans hnorm

/-- Each actual positive Gram eigenvalue is bounded below by the squared
inverse of the Moore--Penrose operator norm. The nonzero eigenvector in
`HasEigenvalue` is used to cancel its norm. -/
theorem one_le_eigenvalue_mul_norm_sq
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (hMP : IsMoorePenroseInverseCLM A B)
    {r : ℝ} (hr : 0 < r)
    (heigen : Module.End.HasEigenvalue (A.comp A.adjoint).toLinearMap (r : 𝕜)) :
    1 ≤ r * ‖B‖ ^ 2 := by
  obtain ⟨y, hy⟩ := heigen.exists_hasEigenvector
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy.2
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hop := B.le_opNorm y
  rw [norm_apply_of_mem_eigenspace A B hMP r hr hy.1] at hop
  have hratio : ‖y‖ ≤ (‖B‖ * ‖y‖) * Real.sqrt r :=
    (div_le_iff₀ hsqrt_pos).mp hop
  have hbound : 1 ≤ ‖B‖ * Real.sqrt r := by
    apply (mul_le_mul_iff_of_pos_right hy_norm).mp
    calc
      (1 : ℝ) * ‖y‖ = ‖y‖ := one_mul _
      _ ≤ (‖B‖ * ‖y‖) * Real.sqrt r := hratio
      _ = (‖B‖ * Real.sqrt r) * ‖y‖ := mul_right_comm _ _ _
  calc
    1 = (1 : ℝ) * 1 := (one_mul (1 : ℝ)).symm
    _ ≤ (‖B‖ * Real.sqrt r) * (‖B‖ * Real.sqrt r) :=
      mul_le_mul hbound hbound (by norm_num)
        (mul_nonneg (norm_nonneg B) hsqrt_pos.le)
    _ = (Real.sqrt r) ^ 2 * ‖B‖ ^ 2 := by
      rw [← pow_two, mul_pow, mul_comm (‖B‖ ^ 2) ((Real.sqrt r) ^ 2)]
    _ = r * ‖B‖ ^ 2 := by rw [Real.sq_sqrt hr.le]

/-- Arbitrarily small actual positive eigenvalues of the target Gram
operator obstruct closed range. This is a one-way point-spectrum criterion;
no claim of a complete eigenbasis or converse criterion is made. -/
theorem not_isClosed_range_of_positive_eigenvalues_arbitrarily_small
    (A : E →L[𝕜] F)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r < ε ∧
      Module.End.HasEigenvalue (A.comp A.adjoint).toLinearMap (r : 𝕜)) :
    ¬ IsClosed (A.range : Set F) := by
  intro hClosed
  let B := moorePenroseInverse A hClosed
  have hMP : IsMoorePenroseInverseCLM A B :=
    isMoorePenroseInverse_moorePenroseInverse A hClosed
  have hden : 0 < ‖B‖ ^ 2 + 1 := by positivity
  obtain ⟨r, hr, hr_small, heigen⟩ :=
    hsmall (1 / (‖B‖ ^ 2 + 1)) (div_pos zero_lt_one hden)
  have hlower := one_le_eigenvalue_mul_norm_sq A B hMP hr heigen
  have hupper : r * (‖B‖ ^ 2 + 1) < 1 := (lt_div_iff₀ hden).mp hr_small
  have hstrict : r * ‖B‖ ^ 2 < r * (‖B‖ ^ 2 + 1) :=
    mul_lt_mul_of_pos_left (lt_add_one _) hr
  exact (not_lt_of_ge hlower) (hstrict.trans hupper)

end InfoGeometry.Analysis.HilbertGramMoorePenrose
