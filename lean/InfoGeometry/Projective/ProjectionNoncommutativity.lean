/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Noncommutativity of projective incidence operators

The carrier is the full algebra `E →L[ℂ] E`. Points are native projective
points; their operators are the canonical orthogonal projections onto their
one-dimensional submodules. No simultaneous diagonalization is assumed.
-/

noncomputable section

namespace InfoGeometry.Projective.ProjectionNoncommutativity

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Different projective points are disjoint one-dimensional submodules. -/
theorem disjoint_rays {p q : Projectivization ℂ E} (hpq : p ≠ q) :
    Disjoint p.submodule q.submodule := by
  have hp : IsAtom p.submodule :=
    Submodule.isAtom_iff_finrank_eq_one.mpr p.finrank_submodule
  have hq : IsAtom q.submodule :=
    Submodule.isAtom_iff_finrank_eq_one.mpr q.finrank_submodule
  exact hp.disjoint_of_ne hq (fun h => hpq (Projectivization.submodule_injective h))

/-- Distinct rays commute as orthogonal projections exactly when they are orthogonal.
This is a theorem about arbitrary bounded operators on the given inner-product space. -/
theorem commute_ray_projections_iff_of_ne {p q : Projectivization ℂ E}
    (hpq : p ≠ q) :
    Commute p.submodule.starProjection q.submodule.starProjection ↔
      p.submodule ⟂ q.submodule := by
  constructor
  · intro hcomm
    apply Submodule.starProjection_comp_starProjection_eq_zero_iff.mp
    apply ContinuousLinearMap.ext
    intro x
    change p.submodule.starProjection (q.submodule.starProjection x) = 0
    apply (Submodule.disjoint_def.mp (disjoint_rays hpq))
    · exact p.submodule.starProjection_apply_mem _
    · apply Submodule.starProjection_eq_self_iff.mp
      have hc := DFunLike.congr_fun hcomm.eq (q.submodule.starProjection x)
      change p.submodule.starProjection
          (q.submodule.starProjection (q.submodule.starProjection x)) =
        q.submodule.starProjection
          (p.submodule.starProjection (q.submodule.starProjection x)) at hc
      have hqq : q.submodule.starProjection (q.submodule.starProjection x) =
          q.submodule.starProjection x :=
        Submodule.starProjection_eq_self_iff.mpr
          (q.submodule.starProjection_apply_mem x)
      simpa only [hqq] using hc.symm
  · intro horth
    change p.submodule.starProjection ∘L q.submodule.starProjection =
      q.submodule.starProjection ∘L p.submodule.starProjection
    exact horth.starProjection_comp_starProjection.trans
      horth.symm.starProjection_comp_starProjection.symm

/-- Complete classification, including the coincident-point case. -/
theorem commute_ray_projections_iff (p q : Projectivization ℂ E) :
    Commute p.submodule.starProjection q.submodule.starProjection ↔
      p = q ∨ p.submodule ⟂ q.submodule := by
  by_cases hpq : p = q
  · subst q
    exact ⟨fun _ => Or.inl rfl, fun _ => Commute.refl _⟩
  · constructor
    · intro h
      exact Or.inr ((commute_ray_projections_iff_of_ne hpq).mp h)
    · rintro (h | h)
      · exact (hpq h).elim
      · exact (commute_ray_projections_iff_of_ne hpq).mpr h

/-- Each ray gives a genuine self-adjoint idempotent in the operator algebra. -/
theorem ray_projection_isStarProjection [CompleteSpace E]
    (p : Projectivization ℂ E) : IsStarProjection p.submodule.starProjection :=
  isStarProjection_starProjection

/-- Nonzero orthogonal vectors have nonzero sum. -/
theorem orthogonal_sum_ne_zero {u v : E} (hu : u ≠ 0)
    (huv : inner ℂ u v = 0) : u + v ≠ 0 := by
  intro h
  have hh := congrArg (fun w : E => inner ℂ u w) h
  simp only [inner_add_right, huv, add_zero, inner_zero_right] at hh
  exact hu (inner_self_eq_zero.mp hh)

/-- The rays `[u]` and `[u+v]` are different when `u,v` are nonzero orthogonal vectors. -/
theorem orthogonal_pair_rays_ne {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℂ u v = 0) :
    Projectivization.mk ℂ u hu ≠
      Projectivization.mk ℂ (u + v) (orthogonal_sum_ne_zero hu huv) := by
  intro h
  have hs := congrArg (Projectivization.submodule :
    Projectivization ℂ E → Submodule ℂ E) h
  change (ℂ ∙ u) = (ℂ ∙ (u + v)) at hs
  have huv_mem : u + v ∈ (ℂ ∙ u) := by
    rw [hs]
    exact Submodule.mem_span_singleton_self (u + v)
  have hv_mem : v ∈ (ℂ ∙ u) := by
    simpa only [add_sub_cancel_left] using
      (ℂ ∙ u).sub_mem huv_mem (Submodule.mem_span_singleton_self u)
  have hv_orth : v ∈ (ℂ ∙ u)ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huv
  have hvv : inner ℂ v v = 0 :=
    ((ℂ ∙ u).mem_orthogonal v).mp hv_orth v hv_mem
  exact hv (inner_self_eq_zero.mp hvv)

/-- A coordinate-free family of actual noncommuting rank-one projections.
The second projection is onto a superposition of two orthogonal directions. -/
theorem orthogonal_pair_noncommute {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℂ u v = 0) :
    ¬ Commute (ℂ ∙ u).starProjection (ℂ ∙ (u + v)).starProjection := by
  let p := Projectivization.mk ℂ u hu
  let q := Projectivization.mk ℂ (u + v) (orthogonal_sum_ne_zero hu huv)
  have hpq : p ≠ q := orthogonal_pair_rays_ne hu hv huv
  intro hc
  have horth : p.submodule ⟂ q.submodule :=
    (commute_ray_projections_iff_of_ne hpq).mp hc
  have hh : inner ℂ u (u + v) = 0 := horth.inner_eq
    (Submodule.mem_span_singleton_self u)
    (Submodule.mem_span_singleton_self (u + v))
  rw [inner_add_right, huv, add_zero] at hh
  exact hu (inner_self_eq_zero.mp hh)

/-- Every finite-dimensional complex inner-product space of dimension at least two
contains distinct projective points whose canonical projections do not commute. -/
theorem exists_noncommuting_ray_projections [FiniteDimensional ℂ E]
    (hdim : 2 ≤ Module.finrank ℂ E) :
    ∃ p q : Projectivization ℂ E, p ≠ q ∧
      ¬ Commute p.submodule.starProjection q.submodule.starProjection := by
  let b := stdOrthonormalBasis ℂ E
  let i : Fin (Module.finrank ℂ E) := ⟨0, by omega⟩
  let j : Fin (Module.finrank ℂ E) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hu := b.orthonormal.ne_zero i
  have hv := b.orthonormal.ne_zero j
  have huv : inner ℂ (b i) (b j) = 0 := b.orthonormal.inner_eq_zero hij
  refine ⟨Projectivization.mk ℂ (b i) hu,
    Projectivization.mk ℂ (b i + b j) (orthogonal_sum_ne_zero hu huv),
    orthogonal_pair_rays_ne hu hv huv, ?_⟩
  exact orthogonal_pair_noncommute hu hv huv

end InfoGeometry.Projective.ProjectionNoncommutativity
