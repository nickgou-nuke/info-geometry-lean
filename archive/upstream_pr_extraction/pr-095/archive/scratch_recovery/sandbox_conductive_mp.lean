import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

namespace InfoGeometry.Singular.MoorePenrose

section Hilbert
open InnerProductSpace ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Foundation: A bounded operator only 'sees' the component orthogonal to its kernel. -/
theorem map_starProjection_ker_orthogonal_fixed (A : E →L[𝕜] E) (x : E) :
    A (A.kerᗮ.starProjection x) = A x := by
  let K := A.ker
  let Kp := A.kerᗮ
  have hK_closed : IsClosed (K : Set E) := A.isClosed_ker
  haveI : CompleteSpace K := hK_closed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance
  have hsplit : K.starProjection x + Kp.starProjection x = x :=
    Submodule.starProjection_add_starProjection_orthogonal (K := K) x
  have hKzero : A (K.starProjection x) = 0 := 
    LinearMap.mem_ker.1 (Submodule.starProjection_apply_mem K x)
  calc
    A (Kp.starProjection x) = 0 + A (Kp.starProjection x) := (zero_add _).symm
    _ = A (K.starProjection x) + A (Kp.starProjection x) := by rw [hKzero]
    _ = A (K.starProjection x + Kp.starProjection x) := (map_add A _ _).symm
    _ = A x := by rw [hsplit]

/-- L1 Bridge: The restricted bijection between (ker A)ᗮ and range A. -/
theorem exists_restrictedEquiv (A : E →L[𝕜] E) (hClosedRange : IsClosed (A.range : Set E)) :
    ∃ (e : A.kerᗮ ≃L[𝕜] A.range), ∀ x : A.kerᗮ, (e x : E) = A x := by
  classical
  let K := A.ker
  let R := A.range
  let Kp := Kᗮ
  
  haveI : CompleteSpace R := hClosedRange.completeSpace_coe
  haveI : R.HasOrthogonalProjection := inferInstance
  haveI : CompleteSpace Kp := inferInstance
  
  let T : Kp →L[𝕜] R := (A.comp Kp.subtypeL).codRestrict R (fun x => Exists.intro x.1 rfl)
  
  have hTker : (T : Kp →ₗ[𝕜] R).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply Subtype.ext
    have hval : A x.1 = A y.1 := by
      have hval' : (T x : E) = (T y : E) := congrArg Subtype.val hxy
      exact hval'
    have hker : x.1 - y.1 ∈ K := by
      rw [LinearMap.mem_ker, map_sub, hval, sub_self]
    have horth : x.1 - y.1 ∈ Kp := Submodule.sub_mem Kp x.2 y.2
    have hmem : x.1 - y.1 ∈ K ⊓ Kp := ⟨hker, horth⟩
    rw [Submodule.inf_orthogonal_eq_bot K] at hmem
    exact sub_eq_zero.1 hmem

  have hTsurj : (T : Kp →ₗ[𝕜] R).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨Kp.orthogonalProjection x, ?_⟩
    apply Subtype.ext
    dsimp [T]
    rw [ContinuousLinearMap.codRestrict_apply, ContinuousLinearMap.comp_apply, 
        Kp.subtypeL_apply, map_starProjection_ker_orthogonal_fixed]
    exact hx
    
  let e := ContinuousLinearEquiv.ofBijective T hTker hTsurj
  exact ⟨e, fun x => rfl⟩

end Hilbert
end InfoGeometry.Singular.MoorePenrose
