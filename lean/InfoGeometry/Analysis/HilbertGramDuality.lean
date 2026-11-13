/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PartnerEigenspaces
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Eigenspace duality for the two Hilbert Gram operators

For a bounded linear map `A : E →L[𝕜] F` between complete real or complex
inner-product spaces, `A` identifies the native nonzero eigenspaces of
`A† ∘L A` and `A ∘L A†`. The inverse is the scaled adjoint `μ⁻¹ • A†`.
The algebraic equivalence is reused from `PartnerEigenspaces`; this file
upgrades it to a continuous linear equivalence on the native eigenspaces
and proves the inner-product and norm laws for the transported vectors.

Neither ambient space is assumed finite-dimensional. The equality of native
`finrank` readouts describes geometric multiplicities when either eigenspace
is finite-dimensional. No compactness, eigenbasis, spectral completeness,
or short-time Fourier transform is constructed here.
-/

noncomputable section

namespace InfoGeometry.Analysis.HilbertGramDuality

open InfoGeometry.OperatorAlgebra.PartnerEigenspaces
open scoped InnerProduct InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The actual continuous linear equivalence between the nonzero eigenspaces
of the source Gram operator and the target Gram operator. Its underlying
linear equivalence is the existing algebraic partner construction. -/
def gramEigenspaceEquiv (A : E →L[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.eigenspace (A† ∘L A).toLinearMap μ ≃L[𝕜]
      Module.End.eigenspace (A ∘L A†).toLinearMap μ where
  toLinearEquiv := nonzeroEigenspaceEquiv A.toLinearMap A.adjoint.toLinearMap μ hμ
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact A.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (A.adjoint.continuous.comp continuous_subtype_val).const_smul μ⁻¹

@[simp]
theorem gramEigenspaceEquiv_apply (A : E →L[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0)
    (x : Module.End.eigenspace (A† ∘L A).toLinearMap μ) :
    (gramEigenspaceEquiv A μ hμ x : F) = A x := rfl

@[simp]
theorem gramEigenspaceEquiv_symm_apply (A : E →L[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0)
    (y : Module.End.eigenspace (A ∘L A†).toLinearMap μ) :
    ((gramEigenspaceEquiv A μ hμ).symm y : E) = μ⁻¹ • (A†) y := rfl

/-- Transport by `A` retains the eigenvalue and cannot annihilate a nonzero
eigenvector when the eigenvalue is nonzero. -/
theorem apply_hasEigenvector (A : E →L[𝕜] F) {μ : 𝕜} (hμ : μ ≠ 0) {x : E}
    (hx : Module.End.HasEigenvector (A† ∘L A).toLinearMap μ x) :
    Module.End.HasEigenvector (A ∘L A†).toLinearMap μ (A x) := by
  refine ⟨(gramEigenspaceEquiv A μ hμ ⟨x, hx.1⟩).property, ?_⟩
  intro hAx
  have hzero : gramEigenspaceEquiv A μ hμ ⟨x, hx.1⟩ = 0 := by
    apply Subtype.ext
    exact hAx
  have hsource : (⟨x, hx.1⟩ : Module.End.eigenspace (A† ∘L A).toLinearMap μ) = 0 :=
    (gramEigenspaceEquiv A μ hμ).map_eq_zero_iff.mp hzero
  exact hx.2 (congrArg Subtype.val hsource)

/-- The two Hilbert Gram operators have the same nonzero eigenvalues, with
`HasEigenvalue` retaining Mathlib's requirement of a nonzero eigenvector. -/
theorem hasEigenvalue_iff (A : E →L[𝕜] F) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (A† ∘L A).toLinearMap μ ↔
      Module.End.HasEigenvalue (A ∘L A†).toLinearMap μ := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector h
    exact Module.End.hasEigenvalue_of_hasEigenvector (apply_hasEigenvector A hμ hx)
  · intro h
    obtain ⟨y, hy⟩ := Module.End.HasEigenvalue.exists_hasEigenvector h
    have hy' : Module.End.HasEigenvector (A†† ∘L A†).toLinearMap μ y := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using hy
    have htransport := apply_hasEigenvector A.adjoint hμ hy'
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      Module.End.hasEigenvalue_of_hasEigenvector htransport

/-- Finite-dimensionality is an eigenspace condition; no finite-dimensional
hypothesis on either ambient Hilbert space is required. -/
theorem eigenspace_finiteDimensional_iff (A : E →L[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (A† ∘L A).toLinearMap μ) ↔
      FiniteDimensional 𝕜 (Module.End.eigenspace (A ∘L A†).toLinearMap μ) := by
  constructor
  · intro h
    let _ := h
    exact (gramEigenspaceEquiv A μ hμ).toLinearEquiv.finiteDimensional
  · intro h
    let _ := h
    exact (gramEigenspaceEquiv A μ hμ).symm.toLinearEquiv.finiteDimensional

/-- Native finite-rank readouts agree. Together with the preceding theorem,
this gives equality of geometric multiplicities whenever an eigenspace is
finite-dimensional, including on infinite-dimensional ambient spaces. -/
theorem eigenspace_finrank_eq (A : E →L[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (A† ∘L A).toLinearMap μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (A ∘L A†).toLinearMap μ) :=
  (gramEigenspaceEquiv A μ hμ).toLinearEquiv.finrank_eq

/-- On a source Gram eigenspace, applying `A` scales the inner product by
the eigenvalue. Only the second vector needs to lie in that eigenspace. -/
theorem inner_map_map_of_mem_eigenspace (A : E →L[𝕜] F) {μ : 𝕜} {y : E}
    (hy : y ∈ Module.End.eigenspace (A† ∘L A).toLinearMap μ) (x : E) :
    ⟪A x, A y⟫_𝕜 = μ * ⟪x, y⟫_𝕜 := by
  have hy' : (A† ∘L A) y = μ • y := Module.End.mem_eigenspace_iff.mp hy
  calc
    ⟪A x, A y⟫_𝕜 = ⟪x, (A†) (A y)⟫_𝕜 :=
      (A.adjoint_inner_right x (A y)).symm
    _ = μ * ⟪x, y⟫_𝕜 := by
      change ⟪x, (A† ∘L A) y⟫_𝕜 = _
      rw [hy', inner_smul_right]

/-- The vector norm of a transported Gram eigenvector is determined by the
real part of its eigenvalue. The statement also covers the zero vector and
the zero eigenspace. -/
theorem norm_sq_apply_of_mem_eigenspace (A : E →L[𝕜] F) {μ : 𝕜} {x : E}
    (hx : x ∈ Module.End.eigenspace (A† ∘L A).toLinearMap μ) :
    ‖A x‖ ^ 2 = RCLike.re μ * ‖x‖ ^ 2 := by
  have hx' : (A† ∘L A) x = μ • x := Module.End.mem_eigenspace_iff.mp hx
  rw [A.apply_norm_sq_eq_inner_adjoint_right, hx', inner_smul_right,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_mul_ofReal]

/-- The equivalence has the expected norm scaling on its actual native
submodule carriers. -/
theorem norm_sq_gramEigenspaceEquiv (A : E →L[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0)
    (x : Module.End.eigenspace (A† ∘L A).toLinearMap μ) :
    ‖gramEigenspaceEquiv A μ hμ x‖ ^ 2 = RCLike.re μ * ‖x‖ ^ 2 :=
  norm_sq_apply_of_mem_eigenspace A x.property

/-- The source and target Gram operators have equal operator norms, even
when their ambient Hilbert spaces have different dimensions. This uses the
native Hilbert-space C-star norm identity and the isometric adjoint. -/
theorem gram_operator_norm_eq (A : E →L[𝕜] F) :
    ‖A† ∘L A‖ = ‖A ∘L A†‖ := by
  calc
    ‖A† ∘L A‖ = ‖A‖ * ‖A‖ := ContinuousLinearMap.norm_adjoint_comp_self A
    _ = ‖A†‖ * ‖A†‖ := by simp only [LinearIsometryEquiv.norm_map]
    _ = ‖A ∘L A†‖ := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using
        (ContinuousLinearMap.norm_adjoint_comp_self A.adjoint).symm

end InfoGeometry.Analysis.HilbertGramDuality
