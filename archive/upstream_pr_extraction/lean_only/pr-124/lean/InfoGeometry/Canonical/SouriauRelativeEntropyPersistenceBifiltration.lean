import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceCutoffLimit

namespace SouriauRelativeEntropyPersistenceBifiltration

open CategoryTheory
open SouriauRelativeEntropyPersistenceQuotient
open SouriauRelativeEntropyPersistenceFunctor
open SouriauRelativeEntropyPersistenceColimit
open SouriauRelativeEntropyPersistenceCutoff

variable {n : ℕ}

theorem relativeEntropyCutoffTime_interchange
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) {s t : ℝ} (hst : s ≤ t)
    (x : RelativeEntropySublevelQuotient (n := n) ε₂ 0 s) :
    relativeEntropyCutoffQuotientMap hε t
        (relativeEntropySublevelQuotientMap ε₂
          (le_refl 0) hst x) =
      relativeEntropySublevelQuotientMap ε₁
        (le_refl 0) hst
        (relativeEntropyCutoffQuotientMap hε s x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

/-- Combined transport in cutoff and information-time parameters. -/
def relativeEntropyCutoffTimeContinuousMap
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) {s t : ℝ} (hst : s ≤ t) :
    C(RelativeEntropySublevelQuotient (n := n) ε₂ 0 s,
      RelativeEntropySublevelQuotient (n := n) ε₁ 0 t) :=
  (relativeEntropyCutoffQuotientContinuousMap hε t).comp
    (relativeEntropySublevelQuotientContinuousMap ε₂
      (le_refl 0) hst)

@[simp] theorem relativeEntropyCutoffTimeContinuousMap_apply
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) {s t : ℝ} (hst : s ≤ t)
    (x : RelativeEntropySublevelQuotient (n := n) ε₂ 0 s) :
    relativeEntropyCutoffTimeContinuousMap hε hst x =
      relativeEntropyCutoffQuotientMap hε t
        (relativeEntropySublevelQuotientMap ε₂
          (le_refl 0) hst x) := rfl

@[simp] theorem relativeEntropyCutoffTimeContinuousMap_refl
    (ε t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 t) :
    relativeEntropyCutoffTimeContinuousMap
        (le_refl ε) (le_refl t) x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem relativeEntropyCutoffTimeContinuousMap_trans
    {ε₁ ε₂ ε₃ : ℝ} (h₁₂ : ε₁ ≤ ε₂) (h₂₃ : ε₂ ≤ ε₃)
    {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t)
    (x : RelativeEntropySublevelQuotient (n := n) ε₃ 0 r) :
    relativeEntropyCutoffTimeContinuousMap h₁₂ hst
        (relativeEntropyCutoffTimeContinuousMap h₂₃ hrs x) =
      relativeEntropyCutoffTimeContinuousMap
        (h₁₂.trans h₂₃) (hrs.trans hst) x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

/-- The genuine cutoff-time KL persistence bifiltration. -/
noncomputable def relativeEntropyCutoffTimeBifiltration
    (n : ℕ) : (ℝᵒᵖ × ℝ) ⥤ TopCat where
  obj I :=
    TopCat.of
      (RelativeEntropySublevelQuotient
        (n := n) I.1.unop 0 I.2)
  map {I J} h :=
    TopCat.ofHom
      (relativeEntropyCutoffTimeContinuousMap
        (leOfHom h.1.unop) (leOfHom h.2))
  map_id I := by
    apply TopCat.hom_ext
    ext x
    exact
      relativeEntropyCutoffTimeContinuousMap_refl
        I.1.unop I.2 x
  map_comp {I J K} hIJ hJK := by
    apply TopCat.hom_ext
    ext x
    exact
      (relativeEntropyCutoffTimeContinuousMap_trans
        (leOfHom hJK.1.unop) (leOfHom hIJ.1.unop)
        (leOfHom hIJ.2) (leOfHom hJK.2) x).symm

@[simp] theorem relativeEntropyCutoffTimeBifiltration_map_apply
    (n : ℕ) {I J : ℝᵒᵖ × ℝ} (h : I ⟶ J)
    (x : RelativeEntropySublevelQuotient
      (n := n) I.1.unop 0 I.2) :
    (relativeEntropyCutoffTimeBifiltration n).map h x =
      relativeEntropyCutoffTimeContinuousMap
        (leOfHom h.1.unop) (leOfHom h.2) x := by
  rfl

theorem relativeEntropyCutoffTime_to_colimit
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) {s t : ℝ} (hst : s ≤ t)
    (x : RelativeEntropySublevelQuotient (n := n) ε₂ 0 s) :
    relativeEntropyPersistenceCutoffColimitMap hε
        (relativeEntropyPersistenceColimitStage ε₂ s x) =
      relativeEntropyPersistenceColimitStage ε₁ t
        (relativeEntropyCutoffTimeContinuousMap hε hst x) := by
  rw [relativeEntropyPersistenceCutoffColimitMap_stage]
  rw [relativeEntropyPersistenceColimitStage_compat ε₁ hst]
  exact congrArg
    (relativeEntropyPersistenceColimitStage ε₁ t)
    (relativeEntropyCutoffTime_interchange hε hst x).symm

end SouriauRelativeEntropyPersistenceBifiltration
