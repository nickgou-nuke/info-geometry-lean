/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.IncidenceRank
import InfoGeometry.Projective.IncidenceMatroid
import InfoGeometry.Projective.ProjectionIncidence

/-!
# Incidence, rank and noncommutative operator equations

This file proves the translations between the three actual carriers. Rank is
measured on joined operator ranges. The full operator algebra is retained;
no pairwise commutativity condition is used for point-line incidence.
-/

noncomputable section

namespace InfoGeometry.Projective.ProjectionIncidence

open Module IncidenceRank

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- The rank of points is the dimension of the join of their operator ranges. -/
theorem pointRank_eq_finrank_projection_ranges (s : Finset (Projectivization 𝕜 E)) :
    pointRank s = finrank 𝕜 (s.sup fun p => (pointProjection p).range) := by
  simp only [pointProjection_range]
  rfl

/-- Native matroid rank is the rank of the joined operator ranges. -/
theorem matroid_eRk_eq_finrank_projection_ranges (s : Finset (Projectivization 𝕜 E)) :
    (IncidenceMatroid.projectiveMatroid 𝕜 E).eRk (s : Set (Projectivization 𝕜 E)) =
      (finrank 𝕜 (s.sup fun p => (pointProjection p).range) : ℕ∞) :=
  (IncidenceMatroid.projectiveMatroid_eRk_finset s).trans
    (congrArg (fun n : ℕ => (n : ℕ∞)) (pointRank_eq_finrank_projection_ranges s))

/-- Operator absorption is equivalent to absence of growth in range rank. -/
theorem absorption_iff_range_rank_eq {P L : E →L[𝕜] E}
    (hL : IsIdempotentElem L) :
    L * P = P ↔ finrank 𝕜 (P.range ⊔ L.range : Submodule 𝕜 E) = finrank 𝕜 L.range :=
  (range_le_iff_mul_eq hL).symm.trans (subspace_le_iff_finrank_sup_eq P.range L.range)

/-- The rank closure of a finite point set is precisely the fixed-point
incidence relation of the projection onto its span. -/
theorem pointRank_insert_eq_iff_absorption [DecidableEq (Projectivization 𝕜 E)]
    (p : Projectivization 𝕜 E) (s : Finset (Projectivization 𝕜 E)) :
    pointRank (insert p s) = pointRank s ↔
      (pointSpan s).starProjection * pointProjection p = pointProjection p :=
  (pointRank_insert_eq_iff p s).trans (point_incident_iff p (pointSpan s))

/-- Rank at most two is equivalent to a rank-at-most-two star projection
absorbing every point operator. -/
theorem pointRank_le_two_iff_projection (s : Finset (Projectivization 𝕜 E)) :
    pointRank s ≤ 2 ↔
      ∃ L : E →L[𝕜] E, IsStarProjection L ∧ finrank 𝕜 L.range ≤ 2 ∧
        ∀ p ∈ s, L * pointProjection p = pointProjection p := by
  constructor
  · intro hs
    refine ⟨(pointSpan s).starProjection, isStarProjection_starProjection, ?_, ?_⟩
    · simpa only [Submodule.range_starProjection] using hs
    · intro p hp
      exact (point_incident_iff p (pointSpan s)).mp (submodule_le_pointSpan hp)
  · rintro ⟨L, hL, hdim, hpoints⟩
    apply le_trans (Submodule.finrank_mono ((pointSpan_le_iff s L.range).mpr ?_)) hdim
    intro p hp
    have hr := (range_le_iff_mul_eq hL.isIdempotentElem).mpr (hpoints p hp)
    simpa only [pointProjection_range] using hr

/-- Native projective collinearity, rank, and operator absorption agree. -/
theorem isCollinear_iff_projection (s : Finset (Projectivization 𝕜 E)) :
    Projectivization.IsCollinear (s : Set (Projectivization 𝕜 E)) ↔
      ∃ L : E →L[𝕜] E, IsStarProjection L ∧ finrank 𝕜 L.range ≤ 2 ∧
        ∀ p ∈ s, L * pointProjection p = pointProjection p :=
  (isCollinear_iff_pointRank_le_two s).trans (pointRank_le_two_iff_projection s)

/-- Two distinct quotient points determine one and only one rank-two
self-adjoint idempotent, characterized by operator equations. -/
theorem existsUnique_line_projection {p q : Projectivization 𝕜 E} (hpq : p ≠ q) :
    ∃! L : E →L[𝕜] E, IsStarProjection L ∧ finrank 𝕜 L.range = 2 ∧
      L * pointProjection p = pointProjection p ∧
      L * pointProjection q = pointProjection q := by
  let U := p.submodule ⊔ q.submodule
  refine ⟨U.starProjection, ?_, ?_⟩
  · refine ⟨isStarProjection_starProjection, ?_, ?_, ?_⟩
    · rw [Submodule.range_starProjection]
      exact finrank_sup_points hpq
    · exact (point_incident_iff p U).mp le_sup_left
    · exact (point_incident_iff q U).mp le_sup_right
  · rintro L ⟨hL, hdim, hp, hq⟩
    apply ContinuousLinearMap.IsStarProjection.ext hL isStarProjection_starProjection
    rw [Submodule.range_starProjection]
    apply line_eq_span hpq hdim
    · simpa only [pointProjection_range] using (range_le_iff_mul_eq hL.isIdempotentElem).mpr hp
    · simpa only [pointProjection_range] using (range_le_iff_mul_eq hL.isIdempotentElem).mpr hq

/-- Two line operators share a projective point exactly when their joined
range has dimension at most three. This also permits skew lines in dimension four. -/
theorem line_projections_meet_iff {L M : E →L[𝕜] E}
    (hL : IsStarProjection L) (hM : IsStarProjection M)
    (hLdim : finrank 𝕜 L.range = 2) (hMdim : finrank 𝕜 M.range = 2) :
    (∃ p : Projectivization 𝕜 E,
      L * pointProjection p = pointProjection p ∧ M * pointProjection p = pointProjection p) ↔
      finrank 𝕜 (L.range ⊔ M.range : Submodule 𝕜 E) ≤ 3 := by
  simp_rw [← range_le_iff_mul_eq hL.isIdempotentElem,
    ← range_le_iff_mul_eq hM.isIdempotentElem, pointProjection_range]
  exact lines_meet_iff_rank_le_three hLdim hMdim

/-- Distinct rank-two projections in vector dimension three meet in exactly
one native projective point. -/
theorem existsUnique_point_of_line_projections_in_plane
    (hE : finrank 𝕜 E = 3) {L M : E →L[𝕜] E}
    (hL : IsStarProjection L) (hM : IsStarProjection M)
    (hLdim : finrank 𝕜 L.range = 2) (hMdim : finrank 𝕜 M.range = 2) (hne : L ≠ M) :
    ∃! p : Projectivization 𝕜 E,
      L * pointProjection p = pointProjection p ∧ M * pointProjection p = pointProjection p := by
  simp_rw [← range_le_iff_mul_eq hL.isIdempotentElem,
    ← range_le_iff_mul_eq hM.isIdempotentElem, pointProjection_range]
  exact existsUnique_common_point_in_plane hE hLdim hMdim
    (fun h => hne (ContinuousLinearMap.IsStarProjection.ext hL hM h))

end InfoGeometry.Projective.ProjectionIncidence
