import Mathlib
import InfoGeometry.Topology.ChiralLorentzianPlaneTopological

/-!
# Symbolic latent spaces

This file records the minimal topological content of a finite family of
real-valued symbolic observables.  A latent space here is only a topological
space equipped with continuous observables; no probabilistic or physical
interpretation is built in.
-/

namespace InfoGeometry.Topology

abbrev SymbolicLatentObservable (X : Type*) [TopologicalSpace X] := C(X, ℝ)

def SymbolicLatentObservable.fiber
    {X : Type*} [TopologicalSpace X]
    (f : SymbolicLatentObservable X) (value : ℝ) : Set X :=
  f ⁻¹' ({value} : Set ℝ)

theorem isClosed_symbolicLatentObservable_fiber
    {X : Type*} [TopologicalSpace X]
    (f : SymbolicLatentObservable X) (value : ℝ) :
    IsClosed (f.fiber value) := by
  exact isClosed_singleton.preimage f.continuous

abbrev FiniteSymbolicLatentSystem
    (X : Type*) [TopologicalSpace X] (ι : Type*) [Fintype ι] :=
  ι → SymbolicLatentObservable X

namespace FiniteSymbolicLatentSystem

abbrev observable
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : ι → SymbolicLatentObservable X :=
  S

end FiniteSymbolicLatentSystem

def FiniteSymbolicLatentSystem.solutionSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (values : ι → ℝ) : Set X :=
  {x | ∀ i, (S.observable i) x = values i}

def FiniteSymbolicLatentSystem.feasibleSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ) : Set X :=
  {x | ∀ i, (S.observable i) x ∈ targets i}

def symbolicObservationMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : X → (ι → ℝ) :=
  fun x i => (S.observable i) x

theorem continuous_symbolicObservationMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Continuous (symbolicObservationMap S) := by
  exact continuous_pi (fun i => (S.observable i).continuous)

@[simp] theorem symbolicObservationMap_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (x : X) (i : ι) :
    symbolicObservationMap S x i = (S.observable i) x :=
  rfl

def symbolicObservationalSetoid
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : Setoid X where
  r x y := symbolicObservationMap S x = symbolicObservationMap S y
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

theorem symbolicObservationalSetoid_iff
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (x y : X) :
    @Setoid.r X (symbolicObservationalSetoid S) x y ↔
      symbolicObservationMap S x = symbolicObservationMap S y :=
  Iff.rfl

theorem isClosed_finiteSymbolicLatentSystem_feasibleSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsClosed (S.feasibleSet targets) := by
  rw [show S.feasibleSet targets =
      ⋂ i, (S.observable i) ⁻¹' targets i by
    ext x
    simp [FiniteSymbolicLatentSystem.feasibleSet]]
  exact isClosed_iInter (fun i =>
    (hclosed i).preimage (S.observable i).continuous)

theorem isCompact_finiteSymbolicLatentSystem_feasibleSet
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsCompact (S.feasibleSet targets) := by
  exact (isClosed_finiteSymbolicLatentSystem_feasibleSet
    S targets hclosed).isCompact

theorem isClosed_finiteSymbolicLatentSystem_solutionSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    IsClosed (S.solutionSet values) := by
  rw [show S.solutionSet values =
      ⋂ i, (S.observable i).fiber (values i) by
    ext x
    simp [FiniteSymbolicLatentSystem.solutionSet,
      SymbolicLatentObservable.fiber]]
  exact isClosed_iInter (fun i =>
    isClosed_symbolicLatentObservable_fiber (S.observable i) (values i))

theorem finiteSymbolicLatentSystem_solutionSet_eq_feasibleSet_singletons
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    S.solutionSet values = S.feasibleSet (fun i => ({values i} : Set ℝ)) := by
  ext x
  simp [FiniteSymbolicLatentSystem.solutionSet,
    FiniteSymbolicLatentSystem.feasibleSet]

theorem disjoint_solutionSet_of_values_ne
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    {values₁ values₂ : ι → ℝ}
    (hvalues : values₁ ≠ values₂) :
    Disjoint (S.solutionSet values₁) (S.solutionSet values₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  apply hvalues
  funext i
  exact (hx₁ i).symm.trans (hx₂ i)

theorem iUnion_solutionSet_eq_univ
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    (⋃ values : ι → ℝ, S.solutionSet values) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine Set.mem_iUnion.mpr ⟨symbolicObservationMap S x, ?_⟩
    intro i
    rfl

structure SymbolicLatentMorphism
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (T : FiniteSymbolicLatentSystem Y ι) where
  toFun : X → Y
  continuous_toFun : Continuous toFun
  intertwines : ∀ (i : ι) (x : X),
    (T.observable i) (toFun x) = (S.observable i) x

namespace SymbolicLatentMorphism

open CategoryTheory

def id
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    SymbolicLatentMorphism S S where
  toFun := fun x => x
  continuous_toFun := continuous_id
  intertwines := by intro i x; rfl

def comp
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    SymbolicLatentMorphism S U where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  intertwines := by
    intro i x
    change (U.observable i) (g.toFun (f.toFun x)) =
      (S.observable i) x
    rw [g.intertwines, f.intertwines]

theorem map_solutionSet
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    F.toFun '' S.solutionSet values ⊆ T.solutionSet values := by
  rintro y ⟨x, hx, rfl⟩
  intro i
  rw [F.intertwines]
  exact hx i

theorem map_feasibleSet
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (targets : ι → Set ℝ) :
    F.toFun '' S.feasibleSet targets ⊆ T.feasibleSet targets := by
  rintro y ⟨x, hx, rfl⟩
  intro i
  have hobs := F.intertwines i x
  change (T.observable i) (F.toFun x) ∈ targets i
  rw [hobs]
  exact hx i

abbrev feasibleLatentSubspace
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ) :=
  {x : X // x ∈ S.feasibleSet targets}

theorem isClosedEmbedding_feasibleLatentSubspace_subtypeVal
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    Topology.IsClosedEmbedding
      (Subtype.val : feasibleLatentSubspace S targets → X) := by
  exact (isClosed_finiteSymbolicLatentSystem_feasibleSet
    S targets hclosed).isClosedEmbedding_subtypeVal

def feasibleSubspaceMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (targets : ι → Set ℝ) :
    feasibleLatentSubspace S targets → feasibleLatentSubspace T targets :=
  fun x => ⟨F.toFun x, F.map_feasibleSet targets ⟨x, x.property, rfl⟩⟩

theorem continuous_feasibleSubspaceMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (targets : ι → Set ℝ) :
    Continuous (F.feasibleSubspaceMap targets) := by
  exact (F.continuous_toFun.comp continuous_subtype_val).subtype_mk
    (fun x => F.map_feasibleSet targets ⟨x, x.property, rfl⟩)

theorem continuous_solutionSet_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (values : ι → ℝ) :
    ContinuousOn F.toFun (S.solutionSet values) := by
  exact F.continuous_toFun.continuousOn

def quotientMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    _root_.Quotient (symbolicObservationalSetoid S) →
      _root_.Quotient (symbolicObservationalSetoid T) :=
  _root_.Quotient.lift
    (fun x => _root_.Quotient.mk (symbolicObservationalSetoid T) (F.toFun x)) (by
      intro x y h
      apply _root_.Quotient.sound
      change symbolicObservationMap T (F.toFun x) =
        symbolicObservationMap T (F.toFun y)
      calc
        symbolicObservationMap T (F.toFun x) =
            symbolicObservationMap S x := by
              funext i
              exact F.intertwines i x
        _ = symbolicObservationMap S y := h
        _ = symbolicObservationMap T (F.toFun y) := by
              funext i
              exact (F.intertwines i y).symm)

theorem continuous_quotientMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    Continuous F.quotientMap := by
  apply Continuous.quotient_lift
  exact (@continuous_quotient_mk' Y _ (symbolicObservationalSetoid T)).comp
    F.continuous_toFun

@[simp] theorem quotientMap_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) (x : X) :
    F.quotientMap (_root_.Quotient.mk (symbolicObservationalSetoid S) x) =
      _root_.Quotient.mk (symbolicObservationalSetoid T) (F.toFun x) :=
  rfl

theorem quotientMap_id
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι} :
    (SymbolicLatentMorphism.id S).quotientMap = (fun q => q) := by
  funext q
  refine _root_.Quotient.inductionOn q ?_
  intro x
  rfl

theorem quotientMap_comp
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    (SymbolicLatentMorphism.comp g f).quotientMap =
      g.quotientMap ∘ f.quotientMap := by
  funext q
  refine _root_.Quotient.inductionOn q ?_
  intro x
  rfl

end SymbolicLatentMorphism

abbrev feasibleLatentSubspace
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ) :=
  SymbolicLatentMorphism.feasibleLatentSubspace S targets

theorem isCompact_symbolicObservation_image
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsCompact (symbolicObservationMap S '' S.feasibleSet targets) := by
  exact (isCompact_finiteSymbolicLatentSystem_feasibleSet
    S targets hclosed).image
      (continuous_symbolicObservationMap S)

theorem isClosed_symbolicObservation_image
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (hclosed : ∀ i, IsClosed (targets i)) :
    IsClosed (symbolicObservationMap S '' S.feasibleSet targets) := by
  exact (isCompact_symbolicObservation_image S targets hclosed).isClosed

def symbolicObservationQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    _root_.Quotient (symbolicObservationalSetoid S) → (ι → ℝ) :=
  _root_.Quotient.lift (symbolicObservationMap S) (by
    intro x y h
    exact h)

theorem continuous_symbolicObservationQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Continuous (symbolicObservationQuotientMap S) := by
  apply Continuous.quotient_lift
  exact continuous_symbolicObservationMap S

@[simp] theorem symbolicObservationQuotientMap_mk
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (x : X) :
    symbolicObservationQuotientMap S
        (_root_.Quotient.mk (symbolicObservationalSetoid S) x) =
          symbolicObservationMap S x :=
  rfl

theorem injective_symbolicObservationQuotientMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Function.Injective (symbolicObservationQuotientMap S) := by
  intro a
  refine _root_.Quotient.inductionOn a ?_
  intro x b
  refine _root_.Quotient.inductionOn b ?_
  intro y h
  apply _root_.Quotient.sound
  change symbolicObservationMap S x = symbolicObservationMap S y at h
  exact h

noncomputable def symbolicObservationQuotientRangeEquiv
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    _root_.Quotient (symbolicObservationalSetoid S) ≃
      Set.range (symbolicObservationQuotientMap S) :=
  Equiv.ofBijective
    (fun q => ⟨symbolicObservationQuotientMap S q, ⟨q, rfl⟩⟩)
    (by
      constructor
      · intro a b h
        exact injective_symbolicObservationQuotientMap S
          (congrArg Subtype.val h)
      · intro y
        rcases y with ⟨z, hz⟩
        rcases hz with ⟨q, hq⟩
        exact ⟨q, Subtype.ext hq⟩)

@[simp] theorem symbolicObservationQuotientRangeEquiv_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    (symbolicObservationQuotientRangeEquiv S q).1 =
      symbolicObservationQuotientMap S q :=
  rfl

theorem symbolicSolutionSet_eq_observationFiber
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (values : ι → ℝ) :
    S.solutionSet values =
      symbolicObservationMap S ⁻¹' ({values} : Set (ι → ℝ)) := by
  ext x
  constructor
  · intro hx
    funext i
    exact hx i
  · intro hx i
    exact congrFun hx i

structure SymbolicLatentFlow
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) where
  act : ℝ → X → X
  continuous_act : Continuous (fun p : ℝ × X => act p.1 p.2)
  zero_apply : ∀ x, act 0 x = x
  add_apply : ∀ s t x, act (s + t) x = act s (act t x)
  preserves_observation : ∀ s x,
    symbolicObservationMap S (act s x) = symbolicObservationMap S x

namespace SymbolicLatentFlow

theorem continuous_time
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    Continuous (F.act t) := by
  exact F.continuous_act.comp
    (continuous_const.prodMk continuous_id)

theorem maps_solutionSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (values : ι → ℝ) :
    F.act t '' S.solutionSet values ⊆ S.solutionSet values := by
  rintro y ⟨x, hx, rfl⟩
  intro i
  have hobs := congrFun (F.preserves_observation t x) i
  change symbolicObservationMap S (F.act t x) i = values i
  exact hobs.trans (hx i)

theorem maps_solutionSet_eq
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (values : ι → ℝ) :
    F.act t '' S.solutionSet values = S.solutionSet values := by
  apply Set.Subset.antisymm
  · exact maps_solutionSet F t values
  · intro y hy
    refine ⟨F.act (-t) y, maps_solutionSet F (-t) values
      ⟨y, hy, rfl⟩, ?_⟩
    rw [← F.add_apply t (-t) y]
    simp [F.zero_apply]

theorem maps_feasibleSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ) :
    F.act t '' S.feasibleSet targets ⊆ S.feasibleSet targets := by
  rintro y ⟨x, hx, rfl⟩
  intro i
  have hobs := congrFun (F.preserves_observation t x) i
  change symbolicObservationMap S (F.act t x) i ∈ targets i
  rw [hobs]
  exact hx i

theorem maps_feasibleSet_eq
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ) :
    F.act t '' S.feasibleSet targets = S.feasibleSet targets := by
  apply Set.Subset.antisymm
  · exact maps_feasibleSet F t targets
  · intro y hy
    refine ⟨F.act (-t) y, maps_feasibleSet F (-t) targets
      ⟨y, hy, rfl⟩, ?_⟩
    rw [← F.add_apply t (-t) y]
    simp [F.zero_apply]

def feasibleSubspaceMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ) :
    feasibleLatentSubspace S targets → feasibleLatentSubspace S targets :=
  fun x => ⟨F.act t x, F.maps_feasibleSet t targets ⟨x, x.property, rfl⟩⟩

theorem continuous_feasibleSubspaceMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ) :
    Continuous (F.feasibleSubspaceMap t targets) := by
  exact ((F.continuous_time t).comp continuous_subtype_val).subtype_mk
    (fun x => F.maps_feasibleSet t targets ⟨x, x.property, rfl⟩)

theorem feasibleSubspaceMap_comp_neg
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    F.feasibleSubspaceMap t targets
        (F.feasibleSubspaceMap (-t) targets x) = x := by
  apply Subtype.ext
  change F.act t (F.act (-t) (x : X)) = (x : X)
  rw [← F.add_apply t (-t) x]
  simp [F.zero_apply]

def feasibleSubspaceHomeomorph
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ) :
    feasibleLatentSubspace S targets ≃ₜ feasibleLatentSubspace S targets :=
  { toEquiv :=
      { toFun := F.feasibleSubspaceMap t targets
        invFun := F.feasibleSubspaceMap (-t) targets
        left_inv := by
          intro x
          simpa using F.feasibleSubspaceMap_comp_neg (-t) targets x
        right_inv := by
          intro x
          exact F.feasibleSubspaceMap_comp_neg t targets x }
    continuous_toFun := F.continuous_feasibleSubspaceMap t targets
    continuous_invFun := F.continuous_feasibleSubspaceMap (-t) targets }

@[simp] theorem feasibleSubspaceHomeomorph_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    F.feasibleSubspaceHomeomorph t targets x =
      F.feasibleSubspaceMap t targets x :=
  rfl

theorem feasibleSubspaceHomeomorph_zero_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    F.feasibleSubspaceHomeomorph 0 targets x = x := by
  apply Subtype.ext
  simp [feasibleSubspaceHomeomorph, feasibleSubspaceMap, F.zero_apply]

theorem feasibleSubspaceHomeomorph_add_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s t : ℝ) (targets : ι → Set ℝ)
    (x : feasibleLatentSubspace S targets) :
    F.feasibleSubspaceHomeomorph (s + t) targets x =
    F.feasibleSubspaceHomeomorph s targets
        (F.feasibleSubspaceHomeomorph t targets x) := by
  apply Subtype.ext
  change F.act (s + t) (x : X) = F.act s (F.act t (x : X))
  rw [← F.add_apply s t x]
  
end SymbolicLatentFlow

def chiralQuadraticObservable :
    SymbolicLatentObservable (ℝ × ℝ) := {
  toFun := realChiralQuadratic
  continuous_toFun := continuous_realChiralQuadratic }

theorem chiralNullCone_eq_symbolicFiber :
    chiralQuadraticObservable.fiber 0 = realChiralNullCone := by
  rfl

theorem isClosed_chiralSymbolicNullFiber :
    IsClosed (chiralQuadraticObservable.fiber 0) := by
  exact isClosed_symbolicLatentObservable_fiber
    chiralQuadraticObservable 0

def chiralNullSystem :
    FiniteSymbolicLatentSystem (ℝ × ℝ) Unit :=
  fun _ => chiralQuadraticObservable

theorem chiralNullSystem_solutionSet_eq_nullCone :
    chiralNullSystem.solutionSet (fun _ => 0) = realChiralNullCone := by
  ext x
  simp [FiniteSymbolicLatentSystem.solutionSet,
    chiralNullSystem, chiralQuadraticObservable,
    realChiralNullCone]

theorem isClosed_chiralNullSystem_solutionSet :
    IsClosed (chiralNullSystem.solutionSet (fun _ => 0)) := by
  exact isClosed_finiteSymbolicLatentSystem_solutionSet
    chiralNullSystem (fun _ => 0)

def chiralPlusRayObservable :
    SymbolicLatentObservable (ℝ × ℝ) := {
  toFun := fun x => x.2 - x.1
  continuous_toFun := by fun_prop }

def chiralMinusRayObservable :
    SymbolicLatentObservable (ℝ × ℝ) := {
  toFun := fun x => x.2 + x.1
  continuous_toFun := by fun_prop }

def chiralPlusRaySystem :
    FiniteSymbolicLatentSystem (ℝ × ℝ) Unit :=
  fun _ => chiralPlusRayObservable

def chiralMinusRaySystem :
    FiniteSymbolicLatentSystem (ℝ × ℝ) Unit :=
  fun _ => chiralMinusRayObservable

theorem chiralPlusRaySystem_solutionSet_eq_ray :
    chiralPlusRaySystem.solutionSet (fun _ => 0) =
      realChiralNullRayPlus := by
  ext x
  simp [FiniteSymbolicLatentSystem.solutionSet,
    chiralPlusRaySystem, chiralPlusRayObservable,
    realChiralNullRayPlus]
  constructor <;> intro h <;> linarith

theorem chiralMinusRaySystem_solutionSet_eq_ray :
    chiralMinusRaySystem.solutionSet (fun _ => 0) =
      realChiralNullRayMinus := by
  ext x
  simp [FiniteSymbolicLatentSystem.solutionSet,
    chiralMinusRaySystem, chiralMinusRayObservable,
    realChiralNullRayMinus]
  constructor <;> intro h <;> linarith

theorem isClosed_chiralPlusRaySystem_solutionSet :
    IsClosed (chiralPlusRaySystem.solutionSet (fun _ => 0)) := by
  exact isClosed_finiteSymbolicLatentSystem_solutionSet
    chiralPlusRaySystem (fun _ => 0)

theorem isClosed_chiralMinusRaySystem_solutionSet :
    IsClosed (chiralMinusRaySystem.solutionSet (fun _ => 0)) := by
  exact isClosed_finiteSymbolicLatentSystem_solutionSet
    chiralMinusRaySystem (fun _ => 0)

theorem chiralNullSystem_solutionSet_eq_symbolicRayUnion :
    chiralNullSystem.solutionSet (fun _ => 0) =
      chiralPlusRaySystem.solutionSet (fun _ => 0) ∪
        chiralMinusRaySystem.solutionSet (fun _ => 0) := by
  rw [chiralNullSystem_solutionSet_eq_nullCone,
    chiralPlusRaySystem_solutionSet_eq_ray,
    chiralMinusRaySystem_solutionSet_eq_ray,
    realChiralNullCone_eq_nullRays]

theorem chiralRaySystems_intersection_eq_zero :
    chiralPlusRaySystem.solutionSet (fun _ => 0) ∩
        chiralMinusRaySystem.solutionSet (fun _ => 0) =
      ({(0, 0)} : Set (ℝ × ℝ)) := by
  rw [chiralPlusRaySystem_solutionSet_eq_ray,
    chiralMinusRaySystem_solutionSet_eq_ray]
  ext x
  constructor
  · intro hx
    change x.2 = x.1 ∧ x.2 = -x.1 at hx
    have hzero : x.1 = 0 := by linarith [hx.1, hx.2]
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext
    · exact hzero
    · linarith [hx.1]
  · intro hx
    rcases hx with rfl
    simp [realChiralNullRayPlus, realChiralNullRayMinus]

def ObservationsSeparate
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : Prop :=
  Function.Injective (symbolicObservationMap S)

structure SymbolicLatentChart
    (X : Type*) [TopologicalSpace X]
    (ι : Type*) [Fintype ι] where
  system : FiniteSymbolicLatentSystem X ι
  isEmbedding : Topology.IsEmbedding (symbolicObservationMap system)

theorem SymbolicLatentChart.separates
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι) :
    ObservationsSeparate C.system :=
  C.isEmbedding.injective

def chiralFirstObservable :
    SymbolicLatentObservable (ℝ × ℝ) := {
  toFun := Prod.fst
  continuous_toFun := continuous_fst }

def chiralSecondObservable :
    SymbolicLatentObservable (ℝ × ℝ) := {
  toFun := Prod.snd
  continuous_toFun := continuous_snd }

def chiralCoordinateSystem :
    FiniteSymbolicLatentSystem (ℝ × ℝ) (Fin 2) :=
  fun i => if i = 0 then chiralFirstObservable else chiralSecondObservable

theorem chiralCoordinateSystem_observations_separate :
    ObservationsSeparate chiralCoordinateSystem := by
  intro x y h
  apply Prod.ext
  · have h0 := congrFun h (0 : Fin 2)
    simpa [symbolicObservationMap, chiralCoordinateSystem,
      chiralFirstObservable, chiralSecondObservable] using h0
  · have h1 := congrFun h (1 : Fin 2)
    simpa [symbolicObservationMap, chiralCoordinateSystem,
      chiralFirstObservable, chiralSecondObservable] using h1

theorem quotient_mk_injective_of_observations_separate
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (hsep : ObservationsSeparate S) :
    Function.Injective
      (fun x => _root_.Quotient.mk (symbolicObservationalSetoid S) x) := by
  intro x y hxy
  apply hsep
  exact _root_.Quotient.exact hxy

def chiralCoordinateReconstruct (z : Fin 2 → ℝ) : ℝ × ℝ :=
  (z 0, z 1)

theorem continuous_chiralCoordinateReconstruct :
    Continuous chiralCoordinateReconstruct := by
  exact (continuous_apply (0 : Fin 2)).prodMk
    (continuous_apply (1 : Fin 2))

theorem chiralCoordinateReconstruct_leftInverse :
    Function.LeftInverse chiralCoordinateReconstruct
      (symbolicObservationMap chiralCoordinateSystem) := by
  intro x
  apply Prod.ext
  · rfl
  · rfl

theorem chiralCoordinateObservation_isEmbedding :
    Topology.IsEmbedding
      (symbolicObservationMap chiralCoordinateSystem) :=
  chiralCoordinateReconstruct_leftInverse.isEmbedding
    continuous_chiralCoordinateReconstruct
    (continuous_symbolicObservationMap chiralCoordinateSystem)

def chiralCoordinateChart :
    SymbolicLatentChart (ℝ × ℝ) (Fin 2) where
  system := chiralCoordinateSystem
  isEmbedding := chiralCoordinateObservation_isEmbedding

end InfoGeometry.Topology
