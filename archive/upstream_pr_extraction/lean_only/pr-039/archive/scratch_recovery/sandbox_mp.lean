import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

namespace InfoGeometry.Singular.MoorePenrose

-- Postfix for star
local notation:max a "†" => star a

section MP
variable {R : Type*} [Ring R] [StarRing R]

def IsMoorePenroseInverse (A B : R) : Prop :=
  A * B * A = A ∧
  B * A * B = B ∧
  star (A * B) = A * B ∧
  star (B * A) = B * A

namespace IsMoorePenroseInverse

variable {A B : R}

theorem mk
    (h1 : A * B * A = A)
    (h2 : B * A * B = B)
    (h3 : star (A * B) = A * B)
    (h4 : star (B * A) = B * A) :
    IsMoorePenroseInverse A B :=
  ⟨h1, h2, h3, h4⟩

end IsMoorePenroseInverse

end MP

section Hilbert
open InnerProductSpace ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Existence of Moore-Penrose inverse for bounded operators with closed range in Hilbert spaces.

Construction established the conductive path to Mathlib's `orthogonalProjection`.
-/
theorem exists_moorePenroseInverse_of_closedRange
    (A : E →L[ℝ] E)
    (hClosedRange : IsClosed (A.range : Set E)) :
    ∃ (B : E →L[ℝ] E), IsMoorePenroseInverse A B := by
  classical
  let K := A.ker
  let R := A.range
  let Kp := Kᗮ
  
  have hKclosed : IsClosed (K : Set E) := A.isClosed_ker
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  
  letI : CompleteSpace R := hClosedRange.completeSpace_coe
  haveI : R.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace R

  have hK_compl : IsCompl K Kp := Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

  let Ares : Kp →L[ℝ] R :=
    (A.comp Kp.subtypeL).codRestrict R (fun ⟨x, hx⟩ ↦ ⟨x, rfl⟩)

  have hAres_inj : Function.Injective Ares := by
    intro x y hxy
    apply Subtype.ext
    have hval : A x.1 = A y.1 := congrArg Subtype.val hxy
    have hker : (x.1 - y.1) ∈ K := by
      change A (x.1 - y.1) = 0
      rw [map_sub, hval, sub_self]
    have horth : (x.1 - y.1) ∈ Kp := Submodule.sub_mem Kp x.2 y.2
    have hbot : (x.1 - y.1) = 0 := hK_compl.disjoint.le_bot ⟨hker, horth⟩
    exact sub_eq_zero.1 hbot

  have hAres_surj : Function.Surjective Ares := by
    intro ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    let x_kp := Kp.orthogonalProjection x
    refine ⟨x_kp, ?_⟩
    apply Subtype.ext
    dsimp [Ares]
    have hx_split : x = (K.starProjection x : E) + (Kp.starProjection x : E) := by
      rw [← Submodule.starProjection_add_starProjection_orthogonal K x]
    calc
      A x_kp.1 = A (Kp.starProjection x) := by rw [Submodule.starProjection_apply]
      _ = 0 + A (Kp.starProjection x) := by rw [zero_add]
      _ = A (K.starProjection x) + A (Kp.starProjection x) := by
        have hxk : (K.starProjection x : E) ∈ K := (K.orthogonalProjection x).2
        rw [LinearMap.mem_ker.1 hxk]
      _ = A (K.starProjection x + Kp.starProjection x) := by rw [map_add]
      _ = A x := by rw [hx_split]

  let e : Kp ≃L[ℝ] R := 
    ContinuousLinearEquiv.ofBijective Ares (LinearMap.ker_eq_bot.2 hAres_inj) (LinearMap.range_eq_top.2 hAres_surj)
  
  let B : E →L[ℝ] E := Kp.subtypeL.comp (e.symm.toContinuousLinearMap.comp R.orthogonalProjection)

  have hAB : A.comp B = R.starProjection := by
    ext x
    dsimp [B]
    have hstep : Ares (e.symm (R.orthogonalProjection x)) = R.orthogonalProjection x := 
      e.apply_symm_apply (R.orthogonalProjection x)
    rw [Submodule.starProjection_apply]
    exact congrArg Subtype.val hstep

  have hBA : B.comp A = Kp.starProjection := by
    ext x
    dsimp [B]
    have hAx : R.orthogonalProjection (A x) = Ares (Kp.orthogonalProjection x) := by
      apply Subtype.ext
      dsimp [Ares]
      have hxR : A x ∈ R := ⟨x, rfl⟩
      rw [Submodule.orthogonalProjection_mem_subspace_eq_self ⟨A x, hxR⟩]
      have hx_split : x = (K.starProjection x : E) + (Kp.starProjection x : E) := 
        (Submodule.starProjection_add_starProjection_orthogonal K x).symm
      rw [hx_split, map_add]
      have hxk : (K.starProjection x : E) ∈ K := (K.orthogonalProjection x).2
      simp [LinearMap.mem_ker.1 hxk]
      rw [Submodule.starProjection_apply]
    rw [hAx, e.symm_apply_apply]
    exact (Submodule.starProjection_apply Kp x).symm

  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · -- A * B * A = A
    change (A.comp B).comp A = A
    rw [hAB]
    ext x
    have hxR : A x ∈ R := ⟨x, rfl⟩
    exact Submodule.starProjection_apply_mem R hxR
  · -- B * A * B = B
    change (B.comp A).comp B = B
    rw [hBA]
    ext x
    have hBmem : B x ∈ Kp := by
      dsimp [B]
      exact (e.symm (R.orthogonalProjection x)).2
    exact Submodule.starProjection_apply_mem Kp hBmem
  · -- star (A * B) = A * B
    show star (A.comp B) = A.comp B
    rw [hAB]
    exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection R)
  · -- star (B * A) = B * A
    show star (B.comp A) = B.comp A
    rw [hBA]
    exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection Kp)

end Hilbert

end InfoGeometry.Singular.MoorePenrose
