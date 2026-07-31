import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceMixedComparison

namespace SouriauRelativeEntropyPersistenceLimitColimitComparison

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceColimit
open SouriauRelativeEntropyPersistenceCutoff
open SouriauRelativeEntropyPersistenceCutoffLimit
open SouriauRelativeEntropyPersistenceBifiltration

/-- The inverse limit of the full cutoff-time KL persistence bifiltration. -/
abbrev RelativeEntropyBifiltrationLimit
    (n : ℕ) : Type :=
  (limit (relativeEntropyCutoffTimeBifiltration n) : TopCat)

/-- Projection from the bifiltration limit to one finite cutoff-time stage. -/
noncomputable def relativeEntropyBifiltrationLimitProjection
    (n : ℕ) (I : ℝᵒᵖ × ℝ) :
    C(RelativeEntropyBifiltrationLimit n,
      (relativeEntropyCutoffTimeBifiltration n).obj I) :=
  (limit.π
    (relativeEntropyCutoffTimeBifiltration n) I).hom

theorem relativeEntropyBifiltrationLimitProjection_compat
    (n : ℕ) {I J : ℝᵒᵖ × ℝ} (h : I ⟶ J)
    (x : RelativeEntropyBifiltrationLimit n) :
    (relativeEntropyCutoffTimeBifiltration n).map h
        (relativeEntropyBifiltrationLimitProjection n I x) =
      relativeEntropyBifiltrationLimitProjection n J x := by
  have hw :=
    limit.w (relativeEntropyCutoffTimeBifiltration n) h
  exact congrArg
    (fun k :
      limit (relativeEntropyCutoffTimeBifiltration n) ⟶
        (relativeEntropyCutoffTimeBifiltration n).obj J =>
      k x) hw

/-- Each bifiltration-limit point determines a cutoff-compatible family in
the time colimits, using the canonical stage at information time `0`. -/
noncomputable def relativeEntropyBifiltrationLimitCutoffFamily
    (n : ℕ) :
    RelativeEntropyPersistenceCutoffCompatibleFamily n
      (RelativeEntropyBifiltrationLimit n) where
  map ε :=
    (relativeEntropyPersistenceColimitStage ε 0).comp
      (relativeEntropyBifiltrationLimitProjection n
        (Opposite.op ε, 0))

theorem relativeEntropyBifiltrationLimitCutoffFamily_compatible
    (n : ℕ) :
    ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
      (x : RelativeEntropyBifiltrationLimit n),
      relativeEntropyPersistenceCutoffColimitMap hε
          ((relativeEntropyBifiltrationLimitCutoffFamily n).map ε₂ x) =
        (relativeEntropyBifiltrationLimitCutoffFamily n).map ε₁ x := by
  intro ε₁ ε₂ hε x
  let h :
      (Opposite.op ε₂, (0 : ℝ)) ⟶
        (Opposite.op ε₁, (0 : ℝ)) :=
    ⟨(homOfLE hε).op, homOfLE (le_refl 0)⟩
  change
    relativeEntropyPersistenceCutoffColimitMap hε
        (relativeEntropyPersistenceColimitStage ε₂ 0
          (relativeEntropyBifiltrationLimitProjection n
            (Opposite.op ε₂, 0) x)) =
      relativeEntropyPersistenceColimitStage ε₁ 0
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε₁, 0) x)
  rw [relativeEntropyCutoffTime_to_colimit hε (le_refl 0)]
  exact congrArg
    (relativeEntropyPersistenceColimitStage ε₁ 0)
    (relativeEntropyBifiltrationLimitProjection_compat n h x)

/-- The canonical comparison
`lim_(ε,t) F(ε,t) → lim_ε colim_t F(ε,t)`. -/
noncomputable def relativeEntropyBifiltrationLimitToCutoffLimit
    (n : ℕ) :
    C(RelativeEntropyBifiltrationLimit n,
      RelativeEntropyPersistenceCutoffLimit n) :=
  (relativeEntropyBifiltrationLimitCutoffFamily n).lift
    (relativeEntropyBifiltrationLimitCutoffFamily_compatible n)

/-- The mixed comparison is characterized at every cutoff by the finite
time-zero stage followed by the corresponding bifiltration-limit projection. -/
theorem relativeEntropyBifiltrationLimitToCutoffLimit_projection
    (n : ℕ) (ε : ℝ)
    (x : RelativeEntropyBifiltrationLimit n) :
    relativeEntropyPersistenceCutoffLimitProjection n ε
        (relativeEntropyBifiltrationLimitToCutoffLimit n x) =
      relativeEntropyPersistenceColimitStage ε 0
        (relativeEntropyBifiltrationLimitProjection n
          (Opposite.op ε, 0) x) := by
  exact
    RelativeEntropyPersistenceCutoffCompatibleFamily.projection_lift
      (relativeEntropyBifiltrationLimitCutoffFamily n)
      (relativeEntropyBifiltrationLimitCutoffFamily_compatible n) ε x

/-- The comparison map is the unique continuous map with the stated
cutoffwise time-zero factorization. -/
theorem relativeEntropyBifiltrationLimitToCutoffLimit_unique
    (n : ℕ)
    (g :
      C(RelativeEntropyBifiltrationLimit n,
        RelativeEntropyPersistenceCutoffLimit n))
    (hg :
      ∀ (ε : ℝ) (x : RelativeEntropyBifiltrationLimit n),
        relativeEntropyPersistenceCutoffLimitProjection n ε (g x) =
          relativeEntropyPersistenceColimitStage ε 0
            (relativeEntropyBifiltrationLimitProjection n
              (Opposite.op ε, 0) x)) :
    g = relativeEntropyBifiltrationLimitToCutoffLimit n := by
  exact
    RelativeEntropyPersistenceCutoffCompatibleFamily.lift_unique
      (relativeEntropyBifiltrationLimitCutoffFamily n)
      (relativeEntropyBifiltrationLimitCutoffFamily_compatible n) g hg

end SouriauRelativeEntropyPersistenceLimitColimitComparison
