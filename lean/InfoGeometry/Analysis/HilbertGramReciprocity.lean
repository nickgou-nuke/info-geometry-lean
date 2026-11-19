/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.HilbertGramDuality
import Mathlib.Analysis.Real.Sqrt

/-!
# Isometric reciprocity on positive Gram eigenspaces

For a bounded map `A : E →L[𝕜] F` between complete real or complex Hilbert
spaces, the existing `HilbertGramDuality.gramEigenspaceEquiv` identifies the
nonzero eigenspaces of `A† ∘L A` and `A ∘L A†`. Here its normalization by the
inverse square root of a positive real eigenvalue is packaged as a native
`LinearIsometryEquiv`. The inverse is the same normalization of `A†`.

The ambient spaces may have unequal or infinite dimension. The positivity
statements require an actual `HasEigenvalue` witness, which supplies a nonzero
eigenvector. They do not infer positivity from a nonzero scalar alone.

This is an equivalence on a specified eigenspace, not a global inverse or
Moore--Penrose inverse of `A`. It does not assert spectral completeness,
compactness, a zero-mode index, a trace identity, or an unbounded-operator
domain theorem. The specialized fixed-value normalization in
`Canonical.RealCl55NativeChiralHodgeIndexBridge` has a different carrier;
the present construction uses native Gram eigenspaces throughout.
-/

noncomputable section

namespace InfoGeometry.Analysis.HilbertGramReciprocity

open scoped InnerProduct InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every actual Gram eigenvalue is real and nonnegative. The nonzero-vector
part of `HasEigenvalue` is essential: it permits division by the squared norm
when extracting the eigenvalue from the Gram inner-product identity. -/
theorem gram_eigenvalue_real_nonneg (A : E →L[𝕜] F) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (A† ∘L A).toLinearMap μ) :
    (RCLike.re μ : 𝕜) = μ ∧ 0 ≤ RCLike.re μ := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx_norm_ne : (‖x‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx.2)
  have hinner : (‖A x‖ : 𝕜) ^ 2 = μ * (‖x‖ : 𝕜) ^ 2 := by
    simpa only [inner_self_eq_norm_sq_to_K] using
      HilbertGramDuality.inner_map_map_of_mem_eigenspace A hx.1 x
  have hratio : μ = ((‖A x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_div, RCLike.ofReal_pow, RCLike.ofReal_pow]
    exact (eq_div_iff (pow_ne_zero 2 hx_norm_ne)).2 hinner.symm
  have hre : RCLike.re μ = ‖A x‖ ^ 2 / ‖x‖ ^ 2 := by
    rw [hratio, RCLike.ofReal_re]
  constructor
  · rw [hre]
    exact hratio.symm
  · rw [hre]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- A nonzero actual Gram eigenvalue has strictly positive real part.
No positivity or spectral-completeness assumption is imposed on `A`. -/
theorem gram_eigenvalue_re_pos (A : E →L[𝕜] F) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (A† ∘L A).toLinearMap μ) (hμ0 : μ ≠ 0) :
    0 < RCLike.re μ := by
  obtain ⟨hreal, hnonneg⟩ := gram_eigenvalue_real_nonneg A hμ
  by_contra h
  have hz : RCLike.re μ = 0 := le_antisymm (not_lt.mp h) hnonneg
  apply hμ0
  rw [← hreal, hz, RCLike.ofReal_zero]

/-- The normalized Gram correspondence is a genuine linear isometric
equivalence. Its underlying linear equivalence is the existing Gram
correspondence followed by native multiplication by a nonzero scalar. -/
def normalizedGramEigenspaceEquiv (A : E →L[𝕜] F) (r : ℝ) (hr : 0 < r) :
    Module.End.eigenspace (A† ∘L A).toLinearMap (r : 𝕜) ≃ₗᵢ[𝕜]
      Module.End.eigenspace (A ∘L A†).toLinearMap (r : 𝕜) :=
  let e := (HilbertGramDuality.gramEigenspaceEquiv A (r : 𝕜)
    (RCLike.ofReal_ne_zero.mpr hr.ne')).toLinearEquiv
  let c : 𝕜 := (((Real.sqrt r)⁻¹ : ℝ) : 𝕜)
  have hc : c ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr hr).ne')
  (e.trans (LinearEquiv.smulOfNeZero 𝕜 _ c hc)).isometryOfInner (by
    intro x y
    change ⟪c • A (x : E), c • A (y : E)⟫_𝕜 = ⟪(x : E), (y : E)⟫_𝕜
    have hscale_real : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * r = 1 := by
      calc
        (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * r =
            (Real.sqrt r * Real.sqrt r)⁻¹ * r := by rw [mul_inv_rev]
        _ = r⁻¹ * r := by rw [Real.mul_self_sqrt hr.le]
        _ = 1 := inv_mul_cancel₀ hr.ne'
    have hscale : c * c * (r : 𝕜) = 1 := by
      dsimp [c]
      exact_mod_cast hscale_real
    have hconj : starRingEnd 𝕜 c = c := by
      dsimp [c]
      exact RCLike.conj_ofReal _
    rw [inner_smul_left, inner_smul_right,
      HilbertGramDuality.inner_map_map_of_mem_eigenspace A y.property (x : E), hconj]
    calc
      c * (c * ((r : 𝕜) * ⟪(x : E), (y : E)⟫_𝕜)) =
          (c * c * (r : 𝕜)) * ⟪(x : E), (y : E)⟫_𝕜 := by simp only [mul_assoc]
      _ = ⟪(x : E), (y : E)⟫_𝕜 := by rw [hscale, one_mul])

/-- The isometry acts by the inverse-square-root normalization of the
original bounded operator on its source Gram eigenspace. -/
@[simp]
theorem normalizedGramEigenspaceEquiv_apply
    (A : E →L[𝕜] F) (r : ℝ) (hr : 0 < r)
    (x : Module.End.eigenspace (A† ∘L A).toLinearMap (r : 𝕜)) :
    (normalizedGramEigenspaceEquiv A r hr x : F) =
      (((Real.sqrt r)⁻¹ : ℝ) : 𝕜) • A x := rfl

/-- The inverse uses the same normalization of the adjoint, with no
global-invertibility hypothesis on `A`. -/
@[simp]
theorem normalizedGramEigenspaceEquiv_symm_apply
    (A : E →L[𝕜] F) (r : ℝ) (hr : 0 < r)
    (y : Module.End.eigenspace (A ∘L A†).toLinearMap (r : 𝕜)) :
    ((normalizedGramEigenspaceEquiv A r hr).symm y : E) =
      (((Real.sqrt r)⁻¹ : ℝ) : 𝕜) • (A†) y := by
  change (r : 𝕜)⁻¹ • (A†) (((((Real.sqrt r)⁻¹ : ℝ) : 𝕜))⁻¹ • (y : F)) = _
  rw [map_smul, smul_smul]
  congr 1
  have hsqrt : (Real.sqrt r : 𝕜) ^ 2 = (r : 𝕜) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have hsqrt_ne : (Real.sqrt r : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  simp only [RCLike.ofReal_inv, inv_inv]
  rw [← hsqrt]
  field_simp [hsqrt_ne]

/-- Applying the normalized correspondence for `A†` agrees with the inverse
correspondence for `A`. The source membership is transported explicitly
through involutivity of the native adjoint. -/
theorem normalizedGramEigenspaceEquiv_adjoint_apply
    (A : E →L[𝕜] F) (r : ℝ) (hr : 0 < r)
    (y : Module.End.eigenspace (A ∘L A†).toLinearMap (r : 𝕜)) :
    (normalizedGramEigenspaceEquiv A.adjoint r hr
      ⟨(y : F), by simpa only [ContinuousLinearMap.adjoint_adjoint] using y.property⟩ : E) =
        ((normalizedGramEigenspaceEquiv A r hr).symm y : E) := by
  rw [normalizedGramEigenspaceEquiv_apply, normalizedGramEigenspaceEquiv_symm_apply]

end InfoGeometry.Analysis.HilbertGramReciprocity
