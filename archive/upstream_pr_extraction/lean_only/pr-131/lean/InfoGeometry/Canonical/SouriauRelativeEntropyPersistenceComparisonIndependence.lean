import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceLimitColimitComparison

namespace SouriauRelativeEntropyPersistenceComparisonIndependence

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceFunctor
open SouriauRelativeEntropyPersistenceColimit
open SouriauRelativeEntropyPersistenceCutoff
open SouriauRelativeEntropyPersistenceCutoffLimit
open SouriauRelativeEntropyPersistenceBifiltration
open SouriauRelativeEntropyPersistenceLimitColimitComparison

/-- Comparable finite stages of a bifiltration-limit point have the same
image in the corresponding cutoff time-colimit. -/
theorem relativeEntropyBifiltrationLimit_stage_eq_of_le
    (n : ℕ) (ε : ℝ) {s t : ℝ} (hst : s ≤ t)
    (x : RelativeEntropyBifiltrationLimit n) :
    relativeEntropyPersistenceColimitStage ε s
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, s) x) =
      relativeEntropyPersistenceColimitStage ε t
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, t) x) := by
  let h :
      (Opposite.op ε, s) ⟶ (Opposite.op ε, t) :=
    ⟨(homOfLE (le_refl ε)).op, homOfLE hst⟩
  have hp :=
    relativeEntropyBifiltrationLimitProjection_compat n h x
  change
    relativeEntropyCutoffQuotientMap (le_refl ε) t
        (relativeEntropySublevelQuotientMap ε
          (le_refl 0) hst
          (relativeEntropyBifiltrationLimitProjection n
            (Opposite.op ε, s) x)) =
      relativeEntropyBifiltrationLimitProjection n
        (Opposite.op ε, t) x at hp
  rw [relativeEntropyCutoffQuotientMap_refl] at hp
  calc
    relativeEntropyPersistenceColimitStage ε s
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, s) x) =
      relativeEntropyPersistenceColimitStage ε t
        (relativeEntropySublevelQuotientMap ε
          (le_refl 0) hst
          (relativeEntropyBifiltrationLimitProjection n
            (Opposite.op ε, s) x)) := by
        exact
          relativeEntropyPersistenceColimitStage_compat
            ε hst _
    _ =
      relativeEntropyPersistenceColimitStage ε t
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, t) x) := by
        exact congrArg
          (relativeEntropyPersistenceColimitStage ε t) hp

/-- A point of the bifiltration limit has the same image in a fixed cutoff
time-colimit, independently of the finite time stage used to represent it. -/
theorem relativeEntropyBifiltrationLimit_stage_independent
    (n : ℕ) (ε s t : ℝ)
    (x : RelativeEntropyBifiltrationLimit n) :
    relativeEntropyPersistenceColimitStage ε s
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, s) x) =
      relativeEntropyPersistenceColimitStage ε t
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, t) x) := by
  rcases le_total s t with hst | hts
  · exact
      relativeEntropyBifiltrationLimit_stage_eq_of_le
        n ε hst x
  · exact
      (relativeEntropyBifiltrationLimit_stage_eq_of_le
        n ε hts x).symm

/-- The cutoff-compatible family obtained from an arbitrary reference time. -/
noncomputable def relativeEntropyBifiltrationLimitCutoffFamilyAt
    (n : ℕ) (t : ℝ) :
    RelativeEntropyPersistenceCutoffCompatibleFamily n
      (RelativeEntropyBifiltrationLimit n) where
  map ε :=
    (relativeEntropyPersistenceColimitStage ε t).comp
      (relativeEntropyBifiltrationLimitProjection n
        (Opposite.op ε, t))

theorem relativeEntropyBifiltrationLimitCutoffFamilyAt_compatible
    (n : ℕ) (t : ℝ) :
    ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
      (x : RelativeEntropyBifiltrationLimit n),
      relativeEntropyPersistenceCutoffColimitMap hε
          ((relativeEntropyBifiltrationLimitCutoffFamilyAt n t).map ε₂ x) =
        (relativeEntropyBifiltrationLimitCutoffFamilyAt n t).map ε₁ x := by
  intro ε₁ ε₂ hε x
  let h :
      (Opposite.op ε₂, t) ⟶
        (Opposite.op ε₁, t) :=
    ⟨(homOfLE hε).op, homOfLE (le_refl t)⟩
  change
    relativeEntropyPersistenceCutoffColimitMap hε
        (relativeEntropyPersistenceColimitStage ε₂ t
          (relativeEntropyBifiltrationLimitProjection n
            (Opposite.op ε₂, t) x)) =
      relativeEntropyPersistenceColimitStage ε₁ t
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε₁, t) x)
  rw [relativeEntropyCutoffTime_to_colimit hε (le_refl t)]
  exact congrArg
    (relativeEntropyPersistenceColimitStage ε₁ t)
    (relativeEntropyBifiltrationLimitProjection_compat n h x)

/-- The mixed limit-colimit comparison formed at reference time `t`. -/
noncomputable def relativeEntropyBifiltrationLimitToCutoffLimitAt
    (n : ℕ) (t : ℝ) :
    C(RelativeEntropyBifiltrationLimit n,
      RelativeEntropyPersistenceCutoffLimit n) :=
  (relativeEntropyBifiltrationLimitCutoffFamilyAt n t).lift
    (relativeEntropyBifiltrationLimitCutoffFamilyAt_compatible n t)

@[simp] theorem
    relativeEntropyBifiltrationLimitToCutoffLimitAt_projection
    (n : ℕ) (t ε : ℝ)
    (x : RelativeEntropyBifiltrationLimit n) :
    relativeEntropyPersistenceCutoffLimitProjection n ε
        (relativeEntropyBifiltrationLimitToCutoffLimitAt n t x) =
      relativeEntropyPersistenceColimitStage ε t
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, t) x) := by
  exact
    RelativeEntropyPersistenceCutoffCompatibleFamily.projection_lift
      (relativeEntropyBifiltrationLimitCutoffFamilyAt n t)
      (relativeEntropyBifiltrationLimitCutoffFamilyAt_compatible n t) ε x

/-- The canonical mixed comparison does not depend on the chosen finite
reference time. -/
theorem relativeEntropyBifiltrationLimitToCutoffLimitAt_eq
    (n : ℕ) (s t : ℝ) :
    relativeEntropyBifiltrationLimitToCutoffLimitAt n s =
      relativeEntropyBifiltrationLimitToCutoffLimitAt n t := by
  apply
    RelativeEntropyPersistenceCutoffCompatibleFamily.lift_unique
      (relativeEntropyBifiltrationLimitCutoffFamilyAt n t)
      (relativeEntropyBifiltrationLimitCutoffFamilyAt_compatible n t)
  intro ε x
  rw [
    relativeEntropyBifiltrationLimitToCutoffLimitAt_projection]
  exact
    relativeEntropyBifiltrationLimit_stage_independent
      n ε s t x

/-- Every reference-time construction agrees with the time-zero comparison
defined in the mixed limit-colimit owner module. -/
theorem relativeEntropyBifiltrationLimitToCutoffLimitAt_eq_canonical
    (n : ℕ) (t : ℝ) :
    relativeEntropyBifiltrationLimitToCutoffLimitAt n t =
      relativeEntropyBifiltrationLimitToCutoffLimit n := by
  apply
    RelativeEntropyPersistenceCutoffCompatibleFamily.lift_unique
      (relativeEntropyBifiltrationLimitCutoffFamily n)
      (relativeEntropyBifiltrationLimitCutoffFamily_compatible n)
  intro ε x
  rw [
    relativeEntropyBifiltrationLimitToCutoffLimitAt_projection]
  exact
    relativeEntropyBifiltrationLimit_stage_independent
      n ε t 0 x

end SouriauRelativeEntropyPersistenceComparisonIndependence
