import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

open InnerProductSpace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

lemma map_starProjection_ker_orthogonal (A : E →L[𝕜] E) (x : E) :
    A (A.kerᗮ.starProjection x) = A x := by
  let K := A.ker
  let Kp := Kᗮ
  haveI : CompleteSpace K := A.isClosed_ker.completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  have hsplit : K.starProjection x + Kp.starProjection x = x :=
    Submodule.starProjection_add_starProjection_orthogonal (K := K) x
  have hKzero : A (K.starProjection x) = 0 :=
    LinearMap.mem_ker.1 (Submodule.starProjection_apply_mem K x)
  calc
    A (Kp.starProjection x) = 0 + A (Kp.starProjection x) := by rw [zero_add]
    _ = A (K.starProjection x) + A (Kp.starProjection x) := by rw [hKzero]
    _ = A (K.starProjection x + Kp.starProjection x) := by rw [map_add]
    _ = A x := by rw [hsplit]

def Ares (A : E →L[𝕜] E) : A.kerᗮ →L[𝕜] A.range :=
  (A.comp A.kerᗮ.subtypeL).codRestrict A.range (fun x => ⟨x.1, rfl⟩)

lemma Ares_injective (A : E →L[𝕜] E) :
    (Ares A : A.kerᗮ →ₗ[𝕜] A.range).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  apply Subtype.ext
  have hval : A x.1 = A y.1 := by
    injection hxy with hval'
    exact hval'
  let K := A.ker
  let Kp := A.kerᗮ
  have hker : x.1 - y.1 ∈ K := by
    rw [LinearMap.mem_ker, map_sub, hval, sub_self]
  have horth : x.1 - y.1 ∈ Kp := Submodule.sub_mem Kp x.2 y.2
  have hbot : x.1 - y.1 = 0 := by
    have : x.1 - y.1 ∈ K ⊓ Kp := Submodule.mem_inf.2 ⟨hker, horth⟩
    simpa [Submodule.inf_orthogonal_eq_bot K] using this
  exact sub_eq_zero.1 hbot

lemma Ares_surjective (A : E →L[𝕜] E) :
    (Ares A : A.kerᗮ →ₗ[𝕜] A.range).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨x, rfl⟩
  let Kp := A.kerᗮ
  refine ⟨Kp.orthogonalProjection x, ?_⟩
  apply Subtype.ext
  simp only [Ares, codRestrict_apply, comp_apply, Kp.subtypeL_apply]
  exact map_starProjection_ker_orthogonal A x
