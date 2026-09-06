import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

namespace InfoGeometry.Singular.MoorePenrose

section MP
variable {R : Type*} [Ring R] [StarRing R]

def IsMoorePenroseInverse (A B : R) : Prop :=
  A * B * A = A ∧
  B * A * B = B ∧
  star (A * B) = A * B ∧
  star (B * A) = B * A

end MP

section Hilbert

open InnerProductSpace ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {𝕜 E : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

private theorem orthogonal_orthogonal_le_of_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮᗮ ≤ U := by
  intro x hx
  have hxker : x ∈ ((Uᗮ).starProjection : E →L[𝕜] E).ker := by
    rw [Submodule.ker_starProjection]
    exact hx
  have hxzero : Uᗮ.starProjection x = 0 := LinearMap.mem_ker.1 hxker
  have hsum : U.starProjection x + Uᗮ.starProjection x = x :=
    Submodule.starProjection_add_starProjection_orthogonal (K := U) x
  have hproj : U.starProjection x = x := by
    rw [hxzero, add_zero] at hsum
    exact hsum
  exact (Submodule.starProjection_eq_self_iff (K := U)).1 hproj

theorem exists_moorePenroseInverse_of_closedRange
    (A : E →L[𝕜] E)
    (hClosedRange : IsClosed (A.range : Set E)) :
    ∃ (B : E →L[𝕜] E), IsMoorePenroseInverse A B := by
  classical

  let K : Submodule 𝕜 E := A.kerᗮ
  let R : Submodule 𝕜 E := A.range

  haveI : CompleteSpace R := hClosedRange.completeSpace_coe
  haveI : R.HasOrthogonalProjection := inferInstance
  haveI : CompleteSpace K := by dsimp [K]; infer_instance
  haveI : K.HasOrthogonalProjection := inferInstance

  have hkerOO : Kᗮ ≤ A.ker := by
    dsimp [K]
    rw [Submodule.orthogonal_orthogonal A.ker]

  have hAproj : ∀ x : E, A (K.starProjection x) = A x := by
    intro x
    have hsum : K.starProjection x + Kᗮ.starProjection x = x :=
      Submodule.starProjection_add_starProjection_orthogonal (K := K) x
    have hkerPart_mem : (Kᗮ.starProjection x : E) ∈ A.ker :=
      hkerOO (Submodule.coe_mem (Kᗮ.orthogonalProjection x))
    calc
      A (K.starProjection x) = A (K.starProjection x) + 0 := (add_zero _).symm
      _ = A (K.starProjection x) + A (Kᗮ.starProjection x) := by
        rw [LinearMap.mem_ker.1 hkerPart_mem]
      _ = A (K.starProjection x + Kᗮ.starProjection x) := by rw [map_add]
      _ = A x := by rw [hsum]

  let T : K →L[𝕜] R := (A.comp K.subtypeL).codRestrict R (fun x => ⟨A x, ⟨x, rfl⟩⟩)

  have hTker : (T : K →ₗ[𝕜] R).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxA : A (x : E) = 0 := by
      have hval : (T x : E) = 0 := congrArg Subtype.val hx
      exact hval
    have hmem : (x : E) ∈ A.ker ⊓ A.kerᗮ := ⟨hxA, x.property⟩
    rw [Submodule.inf_orthogonal_eq_bot A.ker] at hmem
    exact Subtype.ext hmem

  have hTsurj : (T : K →ₗ[𝕜] R).range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨⟨K.starProjection x, Submodule.coe_mem _⟩, ?_⟩
    apply Subtype.ext
    change A (K.starProjection x) = (y : E)
    rw [hAproj x, hx]

  let e : K ≃L[𝕜] R := ContinuousLinearEquiv.ofBijective T hTker hTsurj
  let B : E →L[𝕜] E := K.subtypeL.comp ((e.symm : R →L[𝕜] K).comp R.orthogonalProjection)

  have hAB_apply (x : E) : A (B x) = R.starProjection x := by
    have h := e.apply_symm_apply (R.orthogonalProjection x)
    calc
      A (B x) = (T (e.symm (R.orthogonalProjection x)) : E) := rfl
      _ = (R.orthogonalProjection x : E) := congrArg Subtype.val h
      _ = R.starProjection x := (Submodule.starProjection_apply R x).symm

  have hBA_apply (x : E) : B (A x) = K.starProjection x := by
    let y : R := ⟨A x, ⟨x, rfl⟩⟩
    let z : K := ⟨K.starProjection x, Submodule.coe_mem _⟩
    have hproj : R.orthogonalProjection (A x) = y := by
      apply Subtype.ext; exact Submodule.orthogonalProjection_mem_subspace_eq_self y
    have hTz : T z = y := by
      apply Subtype.ext; exact hAproj x
    have hinv : e.symm (R.orthogonalProjection (A x)) = z := by
      rw [hproj, ← hTz, ContinuousLinearEquiv.symm_apply_apply]
    calc
      B (A x) = (e.symm (R.orthogonalProjection (A x)) : E) := rfl
      _ = (z : E) := congrArg Subtype.val hinv
      _ = K.starProjection x := (Submodule.starProjection_apply K x).symm

  have hAB : A.comp B = R.starProjection := ContinuousLinearMap.ext hAB_apply
  have hBA : B.comp A = K.starProjection := ContinuousLinearMap.ext hBA_apply

  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · show (A.comp B).comp A = A
    rw [hAB]; ext x; exact Submodule.starProjection_apply_mem R ⟨A x, ⟨x, rfl⟩⟩
  · show (B.comp A).comp B = B
    rw [hBA]; ext x; exact Submodule.starProjection_apply_mem K (Submodule.coe_mem (e.symm (R.orthogonalProjection x)))
  · show star (A.comp B) = A.comp B
    rw [hAB]; exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection R)
  · show star (B.comp A) = B.comp A
    rw [hBA]; exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection K)

end Hilbert
end InfoGeometry.Singular.MoorePenrose
