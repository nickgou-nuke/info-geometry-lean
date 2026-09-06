import Mathlib

/-!
# Native finite symbolic-latent core

This file is deliberately independent of the older quotient/flow owners.  It
records only the reusable topological layer: finitely many continuous scalar
observables, their joint readout, fibers, feasible regions, and the induced
observational equivalence relation.
-/

namespace InfoGeometry.Topology

abbrev ContinuousObservable (X : Type*) [TopologicalSpace X] := C(X, ℝ)

abbrev FiniteContinuousObservableSystem
    (X : Type*) [TopologicalSpace X]
    (ι : Type*) [Fintype ι] :=
  ι → ContinuousObservable X

def FiniteContinuousObservableSystem.observationMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    X → (ι → ℝ) :=
  fun x i => S i x

theorem continuous_observationMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Continuous S.observationMap := by
  unfold FiniteContinuousObservableSystem.observationMap
  apply continuous_pi
  intro i
  exact (S i).continuous

def FiniteContinuousObservableSystem.solutionSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (values : ι → ℝ) : Set X :=
  {x | S.observationMap x = values}

def FiniteContinuousObservableSystem.feasibleSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (targets : ι → Set ℝ) : Set X :=
  {x | ∀ i, S i x ∈ targets i}

def latentTargetRegion
    {ι : Type*} [Fintype ι]
    (targets : ι → Set ℝ) : Set (ι → ℝ) :=
  {v | ∀ i, v i ∈ targets i}

theorem feasibleSet_eq_observationMap_preimage_targetRegion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (targets : ι → Set ℝ) :
    S.feasibleSet targets =
      S.observationMap ⁻¹' latentTargetRegion targets := by
  ext x
  rfl

theorem isClosed_solutionSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (values : ι → ℝ) :
    IsClosed (S.solutionSet values) := by
  change IsClosed (S.observationMap ⁻¹' ({values} : Set (ι → ℝ)))
  exact isClosed_singleton.preimage (continuous_observationMap S)

theorem isClosed_feasibleSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsClosed (S.feasibleSet targets) := by
  rw [show S.feasibleSet targets =
      ⋂ i, (S i) ⁻¹' targets i by
    ext x
    simp [FiniteContinuousObservableSystem.feasibleSet]]
  exact isClosed_iInter (fun i =>
    (hclosed i).preimage (S i).continuous)

theorem isCompact_feasibleSet
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsCompact (S.feasibleSet targets) := by
  exact (isClosed_feasibleSet S targets hclosed).isCompact

theorem isCompact_feasible_observation_image
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsCompact (S.observationMap '' S.feasibleSet targets) := by
  exact (isCompact_feasibleSet S targets hclosed).image
    (continuous_observationMap S)

def observationalSetoid
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) : Setoid X where
  r x y := S.observationMap x = S.observationMap y
  iseqv := ⟨
    fun _ => rfl,
    fun h => h.symm,
    fun h₁ h₂ => h₁.trans h₂⟩

theorem observational_equiv_iff
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) (x y : X) :
    @Setoid.r X (observationalSetoid S) x y =
      (S.observationMap x = S.observationMap y) :=
  rfl

abbrev ObservationalQuotient
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :=
  Quotient (observationalSetoid S)

def observationalQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    X → ObservationalQuotient S :=
  Quotient.mk (observationalSetoid S)

def observationalQuotientReadout
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    ObservationalQuotient S → (ι → ℝ) :=
  Quotient.lift (s := observationalSetoid S) S.observationMap (fun _ _ h => h)

theorem continuous_observationalQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Continuous (observationalQuotientMap S) := by
  exact continuous_quot_mk

theorem isQuotientMap_observationalQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Topology.IsQuotientMap (observationalQuotientMap S) := by
  exact isQuotientMap_quot_mk

theorem continuous_observationalQuotientReadout
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Continuous (observationalQuotientReadout S) := by
  exact Continuous.quotient_lift (continuous_observationMap S) (fun _ _ h => h)

theorem observationalQuotientReadout_mk
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) (x : X) :
    observationalQuotientReadout S (observationalQuotientMap S x) =
      S.observationMap x :=
  by
    simpa [observationalQuotientReadout, observationalQuotientMap] using
      (Quotient.lift_mk (s := observationalSetoid S)
        S.observationMap (fun _ _ h => h) x)

theorem observationalQuotientReadout_injective
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Function.Injective (observationalQuotientReadout S) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      exact h

theorem compact_observation_image
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    IsCompact (S.observationMap '' (Set.univ : Set X)) := by
  exact isCompact_univ.image (continuous_observationMap S)

end InfoGeometry.Topology
