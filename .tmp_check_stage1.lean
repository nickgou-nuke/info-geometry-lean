import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

open InnerProductSpace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

lemma map_starProjection_ker_orthogonal (A : E →L[𝕜] E) (x : E) :
    A (A.kerᗮ.starProjection x) = A x := by
  let K := A.ker
  let Kp := Kᗮ
  -- Need to show x = K.starProjection x + Kp.starProjection x
  haveI : CompleteSpace K := A.isClosed_ker.completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  haveI : CompleteSpace Kp := inferInstance
  haveI : Kp.HasOrthogonalProjection := inferInstance
  
  have hsplit : K.starProjection x + Kp.starProjection x = x :=
    Submodule.starProjection_add_starProjection_orthogonal (K := K) x
  
  have hKzero : A (K.starProjection x) = 0 := by
    have hmem : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
    exact LinearMap.mem_ker.1 hmem
  
  calc
    A (Kp.starProjection x) = 0 + A (Kp.starProjection x) := by rw [zero_add]
    _ = A (K.starProjection x) + A (Kp.starProjection x) := by rw [hKzero]
    _ = A (K.starProjection x + Kp.starProjection x) := by rw [map_add]
    _ = A x := by rw [hsplit]
