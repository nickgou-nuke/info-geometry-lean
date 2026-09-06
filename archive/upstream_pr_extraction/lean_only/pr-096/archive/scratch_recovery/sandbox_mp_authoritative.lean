import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section

namespace InfoGeometry.Singular.MoorePenrose

open Function
open ContinuousLinearMap

/-- Moore-Penrose operator-theoretic existence package for bounded operators between Hilbert spaces with closed range.

This version supersedes the old hand-constructed package, following Mathlib v4.28.0 APIs and analytic conventions.
-*/
namespace MoorePenroseClosedRange

variable {𝕜 E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

-- The restriction of `A` to `(ker A)ᗮ`, with codomain `range A`.
def restricted (A : E →L[𝕜] F) : A.kerᗮ →L[𝕜] A.range :=
  A.rangeRestrict ∘L (A.kerᗮ).subtypeL

@[simp]
lemma restricted_coe_apply (A : E →L[𝕜] F) (x : A.kerᗮ) :
    ((restricted A x : A.range) : F) = A (x : E) := rfl

lemma map_starProjection_ker_orthogonal (A : E →L[𝕜] F) (x : E) :
    A ((A.kerᗮ).starProjection x) = A x := by
  haveI : CompleteSpace A.ker := (ContinuousLinearMap.isClosed_ker A).completeSpace_coe
  have hx : x - (A.kerᗮ).starProjection x ∈ A.ker := by
    have hx' : x - (A.kerᗮ).starProjection x ∈ (A.kerᗮ)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := A.kerᗮ) x
    simpa [Submodule.orthogonal_orthogonal] using hx'
  have hzero : A (x - (A.kerᗮ).starProjection x) = 0 := hx
  have hsub : A x - A ((A.kerᗮ).starProjection x) = 0 :=
    simpa [map_sub] using hzero
  exact (sub_eq_zero.mp hsub).symm

lemma restricted_injective (A : E →L[𝕜] F) :
    Function.Injective (restricted A) := by
  intro x y hxy
  apply Subtype.ext
  have hAxy : A (x : E) = A (y : E) := by
    simpa [restricted] using congrArg (fun z : A.range => (z : F)) hxy
  have hker : (x : E) - (y : E) ∈ A.ker := by
    change A ((x : E) - (y : E)) = 0
    simpa [map_sub, hAxy]
  have horth : (x : E) - (y : E) ∈ A.kerᗮ :=
    Submodule.sub_mem (A.kerᗮ) x.property y.property
  have hbot : (x : E) - (y : E) ∈ (⊥ : Submodule 𝕜 E) := by
    have hmem : (x : E) - (y : E) ∈ A.ker ⊓ A.kerᗮ := ⟨hker, horth⟩
    simpa [Submodule.inf_orthogonal_eq_bot (K := A.ker)] using hmem
  have hzero : (x : E) - (y : E) = 0 := by
    simpa using hbot
  exact sub_eq_zero.mp hzero

lemma restricted_surjective (A : E →L[𝕜] F) :
    Function.Surjective (restricted A) := by
  intro y
  rcases y.property with ⟨x, hx⟩
  refine ⟨(A.kerᗮ).orthogonalProjection x, ?_⟩
  apply Subtype.ext
  change A ((A.kerᗮ).starProjection x) = (y : F)
  rw [← hx]
  exact map_starProjection_ker_orthogonal A x

lemma restricted_ker_eq_bot (A : E →L[𝕜] F) :
    (restricted A).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact restricted_injective A

lemma restricted_range_eq_top (A : E →L[𝕜] F) :
    (restricted A).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  exact restricted_surjective A

/-- The continuous linear equivalence `T : (ker A)ᗮ ≃L[𝕜] range A`, via Banach inverse theorem. -/
def restrictedEquiv (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    A.kerᗮ ≃L[𝕜] A.range := by
  haveI : CompleteSpace A.range := hA.completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective
    (restricted A)
    (restricted_ker_eq_bot A)
    (restricted_range_eq_top A)

/-- Moore-Penrose inverse candidate for a closed-range bounded operator: `B = inclusion ∘ T⁻¹ ∘ projection`. -/
def inverse (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    F →L[𝕜] E :=
  letI : CompleteSpace A.range := hA.completeSpace_coe
  (A.kerᗮ).subtypeL ∘L (restrictedEquiv A hA).symm ∘L A.range.orthogonalProjection

lemma inverse_apply_mem_ker_orthogonal
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) (y : F) :
    inverse A hA y ∈ A.kerᗮ := by
  letI : CompleteSpace A.range := hA.completeSpace_coe
  change
    ((((restrictedEquiv A hA).symm (A.range.orthogonalProjection y)) : A.kerᗮ) : E)
      ∈ A.kerᗮ
  exact (((restrictedEquiv A hA).symm (A.range.orthogonalProjection y)) : A.kerᗮ).property

/-- First operator identity: `A ∘ B = projection onto range A`. -/
theorem comp_inverse_eq_rangeProjection
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    A ∘L inverse A hA = A.range.starProjection := by
  letI : CompleteSpace A.range := hA.completeSpace_coe
  apply ContinuousLinearMap.ext
  intro y
  have h :=
    (restrictedEquiv A hA).apply_symm_apply (A.range.orthogonalProjection y)
  have hcoe : A (inverse A hA y) = (A.range.orthogonalProjection y : F) := by
    simpa [inverse, restrictedEquiv, restricted] using
      congrArg (fun z : A.range => (z : F)) h
  calc
    (A ∘L inverse A hA) y = A (inverse A hA y) := rfl
    _ = (A.range.orthogonalProjection y : F) := hcoe
    _ = A.range.starProjection y := rfl

/-- Second operator identity: `B ∘ A = projection onto (ker A)ᗮ`. -/
theorem inverse_comp_eq_kerOrthogonalProjection
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    inverse A hA ∘L A = A.kerᗮ.starProjection := by
  letI : CompleteSpace A.range := hA.completeSpace_coe
  apply ContinuousLinearMap.ext
  intro x

  let kx : A.kerᗮ := (A.kerᗮ).orthogonalProjection x

  have hproj :
      A.range.orthogonalProjection (A x) =
        (⟨A x, ⟨x, rfl⟩⟩ : A.range) := by
    simpa using
      (Submodule.orthogonalProjection_mem_subspace_eq_self
        (K := A.range) (⟨A x, ⟨x, rfl⟩⟩ : A.range))

  have hT : restricted A kx = A.range.orthogonalProjection (A x) := by
    apply Subtype.ext
    change A ((A.kerᗮ).starProjection x) =
      (A.range.orthogonalProjection (A x) : F)
    rw [hproj]
    exact map_starProjection_ker_orthogonal A x

  have hsymm :
      (restrictedEquiv A hA).symm (A.range.orthogonalProjection (A x)) = kx := by
    apply (restrictedEquiv A hA).injective
    calc
      (restrictedEquiv A hA)
          ((restrictedEquiv A hA).symm (A.range.orthogonalProjection (A x)))
          = A.range.orthogonalProjection (A x) :=
            (restrictedEquiv A hA).apply_symm_apply _
      _ = restricted A kx := hT.symm
      _ = (restrictedEquiv A hA) kx := by
        simp [restrictedEquiv]

  calc
    (inverse A hA ∘L A) x =
        ((((restrictedEquiv A hA).symm
          (A.range.orthogonalProjection (A x))) : A.kerᗮ) : E) := rfl
    _ = (kx : E) := congrArg (fun z : A.kerᗮ => (z : E)) hsymm
    _ = A.kerᗮ.starProjection x := rfl

/-- Moore-Penrose identity: `A B A = A`. -/
theorem comp_inverse_comp_eq_self
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    (A ∘L inverse A hA) ∘L A = A := by
  rw [comp_inverse_eq_rangeProjection A hA]
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

/-- Moore-Penrose identity: `B A B = B`. -/
theorem inverse_comp_self_comp_eq_self
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    (inverse A hA ∘L A) ∘L inverse A hA = inverse A hA := by
  rw [inverse_comp_eq_kerOrthogonalProjection A hA]
  apply ContinuousLinearMap.ext
  intro y
  exact Submodule.starProjection_eq_self_iff.mpr
    (inverse_apply_mem_ker_orthogonal A hA y)

/-- Existence package for the Hilbert-space closed-range Moore-Penrose section, with all four relations. -/
theorem exists_inverse
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    ∃ B : F →L[𝕜] E,
      A ∘L B = A.range.starProjection ∧
      B ∘L A = A.kerᗮ.starProjection ∧
      (A ∘L B) ∘L A = A ∧
      (B ∘L A) ∘L B = B := by
  refine ⟨inverse A hA, ?_, ?_, ?_, ?_⟩
  · exact comp_inverse_eq_rangeProjection A hA
  · exact inverse_comp_eq_kerOrthogonalProjection A hA
  · exact comp_inverse_comp_eq_self A hA
  · exact inverse_comp_self_comp_eq_self A hA

end MoorePenroseClosedRange

end InfoGeometry.Singular.MoorePenrose
