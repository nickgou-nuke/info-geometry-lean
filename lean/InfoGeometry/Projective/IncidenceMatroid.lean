/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.IncidenceRank
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# The native matroid of projective points

This constructs Mathlib's `Matroid` on the actual quotient of nonzero vectors,
using independence of representatives. Native projective independence shows
that this is a property of the quotient points. Augmentation and the finite
rank bound are proved from linear independence and subspace dimensions.

The resulting native `Matroid.eRk` is proved equal to the dimension of the span
of representatives, and hence to `IncidenceRank.pointRank` for finite families.
The ambient vector space is explicitly finite-dimensional; its set of
projective points need not be finite.
-/

noncomputable section

open Module Set

namespace InfoGeometry.Projective.IncidenceMatroid

open IncidenceRank

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem independent_encard_eq_finrank_span {I : Set (Projectivization K V)}
    (hI : LinearIndepOn K Projectivization.rep I) :
    I.encard = (finrank K (Submodule.span K (Projectivization.rep '' I)) : ℕ∞) := by
  calc
    I.encard = (Module.rank K (Submodule.span K (Projectivization.rep '' I))).toENat :=
      (toENat_rank_span_set hI).symm
    _ = _ := by rw [← Module.finrank_eq_rank, Cardinal.toENat_nat]

theorem independent_encard_le_finrank {I : Set (Projectivization K V)}
    (hI : LinearIndepOn K Projectivization.rep I) :
    I.encard ≤ (finrank K V : ℕ∞) := by
  simpa only [← Module.finrank_eq_rank, Cardinal.toENat_nat] using
    hI.encard_le_toENat_rank

/-- Augmentation is forced by the dimension inequality between the two spans. -/
theorem independent_augment {I J : Set (Projectivization K V)}
    (hI : LinearIndepOn K Projectivization.rep I)
    (hJ : LinearIndepOn K Projectivization.rep J) (hcard : I.encard < J.encard) :
    ∃ p ∈ J, p ∉ I ∧ LinearIndepOn K Projectivization.rep (insert p I) := by
  have hnot : ¬ Projectivization.rep '' J ⊆
      (Submodule.span K (Projectivization.rep '' I) : Set V) := by
    intro h
    have hdim := Submodule.finrank_mono (Submodule.span_le.mpr h)
    have hdim' :
        (finrank K (Submodule.span K (Projectivization.rep '' J)) : ℕ∞) ≤
          (finrank K (Submodule.span K (Projectivization.rep '' I)) : ℕ∞) :=
      Nat.cast_le.mpr hdim
    rw [← independent_encard_eq_finrank_span hJ,
      ← independent_encard_eq_finrank_span hI] at hdim'
    exact (not_le_of_gt hcard) hdim'
  obtain ⟨v, ⟨p, hpJ, rfl⟩, hp⟩ := Set.not_subset.mp hnot
  refine ⟨p, hpJ, ?_, hI.insert hp⟩
  intro hpI
  exact hp (Submodule.subset_span (R := K) ⟨p, hpI, rfl⟩)

variable (K V) in
/-- The representable projective matroid, using Mathlib's native bounded-augmentation constructor. -/
def projectiveMatroid : Matroid (Projectivization K V) :=
  (IndepMatroid.ofBddAugment Set.univ
    (LinearIndepOn K Projectivization.rep)
    linearIndepOn_empty
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun _ _ hI hJ hcard => independent_augment hI hJ hcard)
    ⟨finrank K V, fun _ hI => independent_encard_le_finrank hI⟩
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] theorem projectiveMatroid_ground :
    (projectiveMatroid K V).E = Set.univ := rfl

@[simp] theorem projectiveMatroid_indep_iff (I : Set (Projectivization K V)) :
    (projectiveMatroid K V).Indep I ↔ LinearIndepOn K Projectivization.rep I :=
  Iff.rfl

/-- The representative-based predicate agrees with native projective independence. -/
theorem projectiveMatroid_indep_iff_projectiveIndependent (I : Set (Projectivization K V)) :
    (projectiveMatroid K V).Indep I ↔
      Projectivization.Independent (fun p : I => (p : Projectivization K V)) :=
  Projectivization.independent_iff.symm

instance projectiveMatroid_rankFinite : (projectiveMatroid K V).RankFinite := by
  unfold projectiveMatroid
  infer_instance

/-- A native matroid basis spans exactly the same vectors as its ambient point set. -/
theorem isBasis'_span_eq {I X : Set (Projectivization K V)}
    (hI : (projectiveMatroid K V).IsBasis' I X) :
    Submodule.span K (Projectivization.rep '' I) =
      Submodule.span K (Projectivization.rep '' X) := by
  have hLI := (projectiveMatroid_indep_iff I).mp hI.indep
  refine le_antisymm (Submodule.span_mono (Set.image_mono hI.subset)) ?_
  apply Submodule.span_le.mpr
  rintro v ⟨p, hpX, rfl⟩
  by_contra hp
  have hInsert : (projectiveMatroid K V).Indep (insert p I) :=
    (projectiveMatroid_indep_iff _).mpr (hLI.insert hp)
  have hpI := hI.mem_of_insert_indep hpX hInsert
  exact hp (Submodule.subset_span (R := K) ⟨p, hpI, rfl⟩)

/-- Native matroid rank agrees with vector-space rank, even for infinite point sets. -/
theorem projectiveMatroid_eRk (X : Set (Projectivization K V)) :
    (projectiveMatroid K V).eRk X =
      (finrank K (Submodule.span K (Projectivization.rep '' X)) : ℕ∞) := by
  obtain ⟨I, hI⟩ := (projectiveMatroid K V).exists_isBasis' X
  have hLI := (projectiveMatroid_indep_iff I).mp hI.indep
  rw [hI.eRk_eq_encard, independent_encard_eq_finrank_span hLI, isBasis'_span_eq hI]

/-- Finite joins of projective rays are exactly spans of their representatives. -/
theorem pointSpan_eq_span_representatives (s : Finset (Projectivization K V)) :
    pointSpan s = Submodule.span K (Projectivization.rep '' (s : Set (Projectivization K V))) := by
  refine le_antisymm ?_ ?_
  · apply (pointSpan_le_iff s _).mpr
    intro p hp
    rw [p.submodule_eq]
    exact Submodule.span_le.mpr (by
      simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using
        (Submodule.subset_span (R := K) (Set.mem_image_of_mem Projectivization.rep hp)))
  · apply Submodule.span_le.mpr
    rintro v ⟨p, hp, rfl⟩
    apply submodule_le_pointSpan hp
    rw [p.submodule_eq]
    exact Submodule.mem_span_singleton_self _

/-- The native matroid and geometric finite-family ranks are the same function. -/
theorem projectiveMatroid_eRk_finset (s : Finset (Projectivization K V)) :
    (projectiveMatroid K V).eRk (s : Set (Projectivization K V)) = (pointRank s : ℕ∞) := by
  rw [projectiveMatroid_eRk, ← pointSpan_eq_span_representatives]
  rfl

/-- The natural-number readout of native matroid rank agrees exactly with geometric rank. -/
theorem projectiveMatroid_eRk_toNat (s : Finset (Projectivization K V)) :
    ((projectiveMatroid K V).eRk (s : Set (Projectivization K V))).toNat = pointRank s := by
  rw [projectiveMatroid_eRk_finset]
  exact ENat.toNat_natCast _

end InfoGeometry.Projective.IncidenceMatroid
