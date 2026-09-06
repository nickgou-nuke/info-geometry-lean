import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceQuotient

namespace SouriauRelativeEntropyPersistenceFunctor

open SouriauRelativeEntropySublevel
open SouriauRelativeEntropySublevelDiagram
open SouriauRelativeEntropyPersistenceQuotient

variable {n : ℕ}

/-- A nested pair of KL persistence intervals induces a map of quotients. -/
def relativeEntropySublevelQuotientMap
    (ε : ℝ) {c d e f : ℝ} (hce : c ≤ e) (hdf : d ≤ f) :
    RelativeEntropySublevelQuotient (n := n) ε c d →
      RelativeEntropySublevelQuotient (n := n) ε e f :=
  Quotient.lift
    (fun p =>
      relativeEntropySublevelQuotientProjection ε e f
        (relativeEntropyCoreSublevelInclusion ε hdf p))
    (by
      intro p q hpq
      apply
        (relativeEntropySublevelQuotientProjection_eq_iff
          ε e f _ _).2
      rcases hpq with rfl | hpq
      · exact Or.inl rfl
      · exact Or.inr
          ⟨relativeEntropyCoreSublevel_mono ε hce hpq.1,
            relativeEntropyCoreSublevel_mono ε hce hpq.2⟩)

@[simp] theorem relativeEntropySublevelQuotientMap_projection
    (ε : ℝ) {c d e f : ℝ} (hce : c ≤ e) (hdf : d ≤ f)
    (p : relativeEntropyCoreSublevel (n := n) ε d) :
    relativeEntropySublevelQuotientMap ε hce hdf
        (relativeEntropySublevelQuotientProjection ε c d p) =
      relativeEntropySublevelQuotientProjection ε e f
        (relativeEntropyCoreSublevelInclusion ε hdf p) := by
  rfl

theorem continuous_relativeEntropySublevelQuotientMap
    (ε : ℝ) {c d e f : ℝ} (hce : c ≤ e) (hdf : d ≤ f) :
    Continuous
      (relativeEntropySublevelQuotientMap
        (n := n) ε hce hdf) := by
  apply
    (isQuotientMap_relativeEntropySublevelQuotientProjection
      (n := n) ε c d).continuous_iff.mpr
  have hcontinuous :
      Continuous
        (relativeEntropySublevelQuotientProjection
            (n := n) ε e f ∘
          relativeEntropyCoreSublevelInclusion
            (n := n) ε hdf) :=
    (continuous_relativeEntropySublevelQuotientProjection
      (n := n) ε e f).comp
        (continuous_relativeEntropyCoreSublevelInclusion
          (n := n) ε hdf)
  simpa only [Function.comp_apply,
    relativeEntropySublevelQuotientMap_projection] using hcontinuous

@[simp] theorem relativeEntropySublevelQuotientMap_refl
    (ε c d : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε c d) :
    relativeEntropySublevelQuotientMap ε
        (le_refl c) (le_refl d) x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem relativeEntropySublevelQuotientMap_trans
    (ε : ℝ) {c d e f g h : ℝ}
    (hce : c ≤ e) (hdf : d ≤ f)
    (heg : e ≤ g) (hfh : f ≤ h)
    (x : RelativeEntropySublevelQuotient (n := n) ε c d) :
    relativeEntropySublevelQuotientMap ε heg hfh
        (relativeEntropySublevelQuotientMap ε hce hdf x) =
      relativeEntropySublevelQuotientMap ε
        (hce.trans heg) (hdf.trans hfh) x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

/-- The induced quotient map as a bundled continuous map. -/
def relativeEntropySublevelQuotientContinuousMap
    (ε : ℝ) {c d e f : ℝ} (hce : c ≤ e) (hdf : d ≤ f) :
    C(RelativeEntropySublevelQuotient (n := n) ε c d,
      RelativeEntropySublevelQuotient (n := n) ε e f) where
  toFun := relativeEntropySublevelQuotientMap ε hce hdf
  continuous_toFun :=
    continuous_relativeEntropySublevelQuotientMap ε hce hdf

@[simp] theorem relativeEntropySublevelQuotientContinuousMap_apply
    (ε : ℝ) {c d e f : ℝ} (hce : c ≤ e) (hdf : d ≤ f)
    (x : RelativeEntropySublevelQuotient (n := n) ε c d) :
    relativeEntropySublevelQuotientContinuousMap ε hce hdf x =
      relativeEntropySublevelQuotientMap ε hce hdf x := rfl

end SouriauRelativeEntropyPersistenceFunctor
