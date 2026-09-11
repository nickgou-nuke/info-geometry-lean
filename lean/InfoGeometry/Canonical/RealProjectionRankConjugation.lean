import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealProjectionRankDoubling
import InfoGeometry.Canonical.RealStageVectorTensorTransport

/-!
# Projection rank and linear conjugation

Ranges of linearly conjugate endomorphisms are linearly equivalent.  This is
the missing invariant needed to transport the product-double rank theorem to
the binary stage-vector carrier.
-/

namespace InfoGeometry.Canonical

def conjugateLinearMap {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (p : V →ₗ[K] V) : W →ₗ[K] W :=
  e.toLinearMap.comp (p.comp e.symm.toLinearMap)

def conjugateRangeMap {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (p : V →ₗ[K] V) :
    LinearMap.range p →ₗ[K] LinearMap.range (conjugateLinearMap e p) where
  toFun x :=
    ⟨e x.1, by
      rcases x.2 with ⟨y, hy⟩
      refine ⟨e y, ?_⟩
      simpa [conjugateLinearMap, LinearMap.comp_apply] using congrArg e hy⟩
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add _ _
  map_smul' c x := by
    apply Subtype.ext
    exact e.map_smul c x.1

theorem conjugateRangeMap_injective {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (p : V →ₗ[K] V) :
    Function.Injective (conjugateRangeMap e p) := by
  intro x y h
  apply Subtype.ext
  apply e.injective
  exact congrArg Subtype.val h

theorem conjugateRangeMap_surjective {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (p : V →ₗ[K] V) :
    Function.Surjective (conjugateRangeMap e p) := by
  intro z
  rcases z.2 with ⟨w, hw⟩
  let x : LinearMap.range p :=
    ⟨e.symm z.1, by
      refine ⟨e.symm w, ?_⟩
      have h' := congrArg e.symm hw
      simpa [conjugateLinearMap, LinearMap.comp_apply] using h'⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact e.apply_symm_apply z.1

noncomputable def conjugateRangeEquiv {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (e : V ≃ₗ[K] W) (p : V →ₗ[K] V) :
    LinearMap.range p ≃ₗ[K] LinearMap.range (conjugateLinearMap e p) :=
  LinearEquiv.ofBijective (conjugateRangeMap e p)
    ⟨conjugateRangeMap_injective e p, conjugateRangeMap_surjective e p⟩

theorem projectionRank_conjugate {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    [FiniteDimensional K V] (e : V ≃ₗ[K] W) (p : V →ₗ[K] V) :
    projectionRank (conjugateLinearMap e p) = projectionRank p := by
  unfold projectionRank
  rw [(conjugateRangeEquiv e p).finrank_eq]

theorem transportedDoubleProjection_rank {n : ℕ}
    (p : RealStageVector n →ₗ[ℝ] RealStageVector n) :
    projectionRank (transportedDoubleProjection p) =
      2 * projectionRank p := by
  let e := (realStageVectorDouble n).symm
  change projectionRank (conjugateLinearMap e (doubleProjection p)) = _
  rw [projectionRank_conjugate]
  exact projectionRank_double p

end InfoGeometry.Canonical
