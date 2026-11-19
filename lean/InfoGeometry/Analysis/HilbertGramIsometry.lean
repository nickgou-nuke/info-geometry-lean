/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.HilbertGramDuality
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Normalized isometry of positive Hilbert Gram eigenspaces

Normalize the existing continuous Gram equivalence by the positive real square
root of the eigenvalue. The carrier remains Mathlib's native eigenspace, and
the result is a native `LinearIsometryEquiv`, for arbitrary complete real or
complex Hilbert spaces. No eigenbasis or discrete-spectrum assumption is used.
-/

noncomputable section

namespace InfoGeometry.Analysis.HilbertGramDuality

open scoped InnerProduct InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Positive real eigenvalues are nonzero in the real or complex scalar field. -/
private theorem positive_scalar_ne_zero {μ : ℝ} (hμ : 0 < μ) : (μ : 𝕜) ≠ 0 := by
  exact_mod_cast ne_of_gt hμ

/-- Normalize the already constructed partner equivalence, rather than
reconstructing the underlying eigenspace bijection. -/
def normalizedGramEigenspaceEquiv (A : E →L[𝕜] F) (μ : ℝ) (hμ : 0 < μ) :
    Module.End.eigenspace (A† ∘L A).toLinearMap (μ : 𝕜) ≃ₗ[𝕜]
      Module.End.eigenspace (A ∘L A†).toLinearMap (μ : 𝕜) :=
  (gramEigenspaceEquiv A (μ : 𝕜) (positive_scalar_ne_zero hμ)).toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero 𝕜 _ (((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) (by
      exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hμ))))

@[simp]
theorem normalizedGramEigenspaceEquiv_apply (A : E →L[𝕜] F) (μ : ℝ)
    (hμ : 0 < μ) (x : Module.End.eigenspace (A† ∘L A).toLinearMap (μ : 𝕜)) :
    (normalizedGramEigenspaceEquiv A μ hμ x : F) =
      (((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) • A x := rfl

/-- The square-root normalization preserves the actual Hilbert inner product. -/
theorem normalizedGramEigenspaceEquiv_inner (A : E →L[𝕜] F) (μ : ℝ)
    (hμ : 0 < μ)
    (x y : Module.End.eigenspace (A† ∘L A).toLinearMap (μ : 𝕜)) :
    ⟪normalizedGramEigenspaceEquiv A μ hμ x,
      normalizedGramEigenspaceEquiv A μ hμ y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  change ⟪(((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) • A x,
      (((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) • A y⟫_𝕜 = ⟪(x : E), (y : E)⟫_𝕜
  rw [inner_smul_left, inner_smul_right,
    inner_map_map_of_mem_eigenspace A y.property (x : E)]
  have hs : (Real.sqrt μ) ^ 2 = μ := Real.sq_sqrt (le_of_lt hμ)
  have hn : (Real.sqrt μ : 𝕜) ≠ 0 := positive_scalar_ne_zero (Real.sqrt_pos.2 hμ)
  have hsK : (Real.sqrt μ : 𝕜) ^ 2 = (μ : 𝕜) := by exact_mod_cast hs
  have hscale : (((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) *
      (((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) * (μ : 𝕜) = 1 := by
    simp only [RCLike.ofReal_inv]
    rw [← hsK]
    field_simp [hn]
  rw [RCLike.conj_ofReal, ← mul_assoc, ← mul_assoc, hscale, one_mul]

/-- The genuine normalized isometry of positive partner eigenspaces. -/
def gramEigenspaceIsometry (A : E →L[𝕜] F) (μ : ℝ) (hμ : 0 < μ) :
    Module.End.eigenspace (A† ∘L A).toLinearMap (μ : 𝕜) ≃ₗᵢ[𝕜]
      Module.End.eigenspace (A ∘L A†).toLinearMap (μ : 𝕜) :=
  (normalizedGramEigenspaceEquiv A μ hμ).isometryOfInner
    (normalizedGramEigenspaceEquiv_inner A μ hμ)

@[simp]
theorem gramEigenspaceIsometry_apply (A : E →L[𝕜] F) (μ : ℝ)
    (hμ : 0 < μ) (x : Module.End.eigenspace (A† ∘L A).toLinearMap (μ : 𝕜)) :
    (gramEigenspaceIsometry A μ hμ x : F) =
      (((Real.sqrt μ)⁻¹ : ℝ) : 𝕜) • A x := rfl

end InfoGeometry.Analysis.HilbertGramDuality
