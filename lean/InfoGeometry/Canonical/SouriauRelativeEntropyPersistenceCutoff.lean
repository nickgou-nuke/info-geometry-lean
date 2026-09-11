import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceUniversal
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace SouriauRelativeEntropyPersistenceCutoff

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropySimplex
open SouriauRelativeEntropySublevel
open SouriauRelativeEntropyPersistenceQuotient
open SouriauRelativeEntropyPersistenceColimit

variable {n : ℕ}

/-- Inclusion from a stricter positive-simplex cutoff into a looser cutoff. -/
def positiveSimplexCorePairCutoffInclusion
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    positiveSimplexCorePair (n := n) ε₂ →
      positiveSimplexCorePair (n := n) ε₁ :=
  fun p =>
    ⟨p.1,
      ⟨⟨p.2.1.1, fun i => hε.trans (p.2.1.2 i)⟩,
        ⟨p.2.2.1, fun i => hε.trans (p.2.2.2 i)⟩⟩⟩

@[simp] theorem positiveSimplexCorePairCutoffInclusion_coe
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    (p : positiveSimplexCorePair (n := n) ε₂) :
    (positiveSimplexCorePairCutoffInclusion hε p :
      (Fin n → ℝ) × (Fin n → ℝ)) = p.1 := rfl

theorem continuous_positiveSimplexCorePairCutoffInclusion
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    Continuous
      (positiveSimplexCorePairCutoffInclusion (n := n) hε) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- Cutoff inclusion restricted to a fixed KL sublevel. -/
def relativeEntropyCoreSublevelCutoffInclusion
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ) :
    relativeEntropyCoreSublevel (n := n) ε₂ t →
      relativeEntropyCoreSublevel (n := n) ε₁ t :=
  fun p =>
    ⟨positiveSimplexCorePairCutoffInclusion hε p.1, p.2⟩

@[simp] theorem relativeEntropyCoreSublevelCutoffInclusion_coe
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ)
    (p : relativeEntropyCoreSublevel (n := n) ε₂ t) :
    (relativeEntropyCoreSublevelCutoffInclusion hε t p :
      positiveSimplexCorePair (n := n) ε₁) =
      positiveSimplexCorePairCutoffInclusion hε p.1 := rfl

theorem continuous_relativeEntropyCoreSublevelCutoffInclusion
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ) :
    Continuous
      (relativeEntropyCoreSublevelCutoffInclusion
        (n := n) hε t) := by
  apply Continuous.subtype_mk
  exact
    (continuous_positiveSimplexCorePairCutoffInclusion
      (n := n) hε).comp continuous_subtype_val

/-- The cutoff inclusion descends to every KL persistence quotient. -/
def relativeEntropyCutoffQuotientMap
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ) :
    RelativeEntropySublevelQuotient (n := n) ε₂ 0 t →
      RelativeEntropySublevelQuotient (n := n) ε₁ 0 t :=
  Quotient.lift
    (fun p =>
      relativeEntropySublevelQuotientProjection ε₁ 0 t
        (relativeEntropyCoreSublevelCutoffInclusion hε t p))
    (by
      intro p q hpq
      apply
        (relativeEntropySublevelQuotientProjection_eq_iff
          ε₁ 0 t _ _).2
      rcases hpq with rfl | hpq
      · exact Or.inl rfl
      · exact Or.inr ⟨hpq.1, hpq.2⟩)

@[simp] theorem relativeEntropyCutoffQuotientMap_projection
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ)
    (p : relativeEntropyCoreSublevel (n := n) ε₂ t) :
    relativeEntropyCutoffQuotientMap hε t
        (relativeEntropySublevelQuotientProjection ε₂ 0 t p) =
      relativeEntropySublevelQuotientProjection ε₁ 0 t
        (relativeEntropyCoreSublevelCutoffInclusion hε t p) := by
  rfl

theorem continuous_relativeEntropyCutoffQuotientMap
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ) :
    Continuous
      (relativeEntropyCutoffQuotientMap (n := n) hε t) := by
  apply
    (isQuotientMap_relativeEntropySublevelQuotientProjection
      (n := n) ε₂ 0 t).continuous_iff.mpr
  have hcontinuous :
      Continuous
        (relativeEntropySublevelQuotientProjection
            (n := n) ε₁ 0 t ∘
          relativeEntropyCoreSublevelCutoffInclusion
            (n := n) hε t) :=
    (continuous_relativeEntropySublevelQuotientProjection
      (n := n) ε₁ 0 t).comp
        (continuous_relativeEntropyCoreSublevelCutoffInclusion
          (n := n) hε t)
  simpa only [Function.comp_apply,
    relativeEntropyCutoffQuotientMap_projection] using hcontinuous

/-- The cutoff quotient map as a bundled continuous map. -/
def relativeEntropyCutoffQuotientContinuousMap
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ) :
    C(RelativeEntropySublevelQuotient (n := n) ε₂ 0 t,
      RelativeEntropySublevelQuotient (n := n) ε₁ 0 t) where
  toFun := relativeEntropyCutoffQuotientMap hε t
  continuous_toFun :=
    continuous_relativeEntropyCutoffQuotientMap hε t

@[simp] theorem relativeEntropyCutoffQuotientMap_refl
    (ε t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 t) :
    relativeEntropyCutoffQuotientMap (le_refl ε) t x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem relativeEntropyCutoffQuotientMap_trans
    {ε₁ ε₂ ε₃ : ℝ} (h₁₂ : ε₁ ≤ ε₂) (h₂₃ : ε₂ ≤ ε₃)
    (t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε₃ 0 t) :
    relativeEntropyCutoffQuotientMap h₁₂ t
        (relativeEntropyCutoffQuotientMap h₂₃ t x) =
      relativeEntropyCutoffQuotientMap (h₁₂.trans h₂₃) t x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

/-- Cutoff monotonicity is a natural transformation of KL persistence rays. -/
noncomputable def relativeEntropyPersistenceCutoffNatTrans
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    relativeEntropyPersistenceRay (n := n) ε₂ ⟶
      relativeEntropyPersistenceRay (n := n) ε₁ where
  app t :=
    TopCat.ofHom
      (relativeEntropyCutoffQuotientContinuousMap hε t)
  naturality := by
    intro s t hst
    apply TopCat.hom_ext
    ext x
    refine Quotient.inductionOn x ?_
    intro p
    rfl

/-- The induced continuous map between cutoff persistence colimits. -/
noncomputable def relativeEntropyPersistenceCutoffColimitMap
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    C(RelativeEntropyPersistenceColimit (n := n) ε₂,
      RelativeEntropyPersistenceColimit (n := n) ε₁) :=
  (colim.map
    (relativeEntropyPersistenceCutoffNatTrans
      (n := n) hε)).hom

theorem relativeEntropyPersistenceCutoffColimitMap_stage
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε₂ 0 t) :
    relativeEntropyPersistenceCutoffColimitMap hε
        (relativeEntropyPersistenceColimitStage ε₂ t x) =
      relativeEntropyPersistenceColimitStage ε₁ t
        (relativeEntropyCutoffQuotientMap hε t x) := by
  have hstage :=
    colimit.ι_map
      (relativeEntropyPersistenceCutoffNatTrans
        (n := n) hε) t
  exact congrArg
    (fun k :
      (relativeEntropyPersistenceRay (n := n) ε₂).obj t ⟶
        colimit (relativeEntropyPersistenceRay (n := n) ε₁) =>
      k x) hstage

end SouriauRelativeEntropyPersistenceCutoff
