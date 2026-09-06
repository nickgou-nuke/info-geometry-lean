import InfoGeometry.Topology.D4StarDiscreteColorFlow

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Continuous observables constant on the centre/outer orbit relation. -/

def OrbitInvariant {Y : Type*} (f : FourPlaneVertex → Y) : Prop :=
  ∀ v w, starOrbitRel v w → f v = f w

def descendObservable
    {Y : Type*} (f : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) : D4StarQuotient → Y :=
  Quotient.lift f (by
    intro v w h
    exact hf v w h)

theorem descendObservable_comp
    {Y : Type*} (f : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) (v : FourPlaneVertex) :
    descendObservable f hf (starQuotientMap v) = f v := rfl

theorem continuous_descendObservable
    {Y : Type*} [TopologicalSpace Y]
    (f : FourPlaneVertex → Y) (hf : OrbitInvariant f)
    (hcont : Continuous f) :
    Continuous (descendObservable f hf) := by
  apply Continuous.quotient_lift
  exact hcont

theorem descendObservable_unique
    {Y : Type*} (f : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) (g : D4StarQuotient → Y)
    (hg : ∀ v, g (starQuotientMap v) = f v) :
    g = descendObservable f hf := by
  funext q
  induction q using Quotient.inductionOn with
  | _ v => exact hg v

def centreOuterObservable : FourPlaneVertex → Bool
  | Sum.inr _ => true
  | Sum.inl _ => false

theorem centreOuterObservable_invariant :
    OrbitInvariant centreOuterObservable := by
  intro v w h
  cases v <;> cases w <;> simp [starOrbitRel, centreOuterObservable] at h ⊢

theorem centreOuterObservable_descends_to_quotient :
    descendObservable centreOuterObservable
      centreOuterObservable_invariant = quotientToBool := by
  funext q
  induction q using Quotient.inductionOn with
  | _ v => rfl

end InfoGeometry.Topology.PauliJungD4Star
