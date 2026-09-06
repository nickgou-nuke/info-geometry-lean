import InfoGeometry.Canonical.FilteredGNSTomitaGraphClosure
import InfoGeometry.Canonical.FilteredGNSHilbertColimitTopology
import InfoGeometry.Canonical.FilteredGNSTomitaDomainTopologicalColimit
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Topological colimit of filtered closed Tomita graphs

The closed Tomita relation is carried by a closed subset of a product of two
completed GNS spaces.  This owner exposes the filtered graph carriers as a
`TopCat` diagram and descends their canonical stage embeddings into the
product of the global GNS colimit with itself.  No boundedness or
single-valuedness of the closed Tomita relation is assumed.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaGraphTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

abbrev graphCarrier (i : I) :=
  {p : (ω.state i).functional.GNS × (ω.state i).functional.GNS //
    p ∈ closedTomitaCoreGraph (ω.state i)}

def graphContinuousMap {i j : I} (hij : i ≤ j) :
    ContinuousMap (graphCarrier Stage sys ω i)
      (graphCarrier Stage sys ω j) :=
  { toFun := fun p =>
      ⟨filteredGNSPairMap Stage sys ω hij p.1,
        filteredGNSPairMap_mapsTo_closedTomitaCoreGraph
          Stage sys ω hij p.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_filteredGNSPairMap Stage sys ω hij).comp
        continuous_subtype_val }

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
@[simp] theorem graphContinuousMap_apply {i j : I} (hij : i ≤ j)
    (p : graphCarrier Stage sys ω i) :
    graphContinuousMap Stage sys ω hij p =
      ⟨filteredGNSPairMap Stage sys ω hij p.1,
        filteredGNSPairMap_mapsTo_closedTomitaCoreGraph
          Stage sys ω hij p.2⟩ :=
  rfl

def graphTopologicalDiagram : I ⥤ TopCat where
  obj i := TopCat.of (graphCarrier Stage sys ω i)
  map f := TopCat.ofHom
    (graphContinuousMap Stage sys ω (leOfHom f))
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    rw [TopCat.id_app]
    change filteredGNSPairMap Stage sys ω (le_refl i) p.1 = p.1
    simp only [filteredGNSPairMap]
    apply Prod.ext
    · exact congrFun (filteredGNSMap_id Stage sys ω i) p.1.1
    · exact congrFun (filteredGNSMap_id Stage sys ω i) p.1.2
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    rw [TopCat.comp_app]
    change
      filteredGNSPairMap Stage sys ω
          (le_trans (leOfHom f) (leOfHom g)) p.1 =
        filteredGNSPairMap Stage sys ω (leOfHom g)
          (filteredGNSPairMap Stage sys ω (leOfHom f) p.1)
    simp only [filteredGNSPairMap]
    apply Prod.ext
    · exact congrFun
        (filteredGNSMap_comp Stage sys ω (leOfHom f) (leOfHom g)).symm
        p.1.1
    · exact congrFun
        (filteredGNSMap_comp Stage sys ω (leOfHom f) (leOfHom g)).symm
        p.1.2

abbrev graphTopologicalColimit : TopCat :=
  colimit (graphTopologicalDiagram Stage sys ω)

def graphTopologicalInjection (i : I) :
    (graphTopologicalDiagram Stage sys ω).obj i ⟶
      graphTopologicalColimit Stage sys ω :=
  colimit.ι (graphTopologicalDiagram Stage sys ω) i

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
theorem graphTopologicalInjection_transition
    {i j : I} (hij : i ≤ j) (p : graphCarrier Stage sys ω i) :
    graphTopologicalInjection Stage sys ω j
        (graphContinuousMap Stage sys ω hij p) =
      graphTopologicalInjection Stage sys ω i p := by
  have h := (colimit.cocone (graphTopologicalDiagram Stage sys ω)).w
    (homOfLE hij)
  exact congrArg (fun f => f p) h

def graphToDomainContinuousMap (i : I) :
    ContinuousMap (graphCarrier Stage sys ω i)
      (closedTomitaDomain (ω.state i)) :=
  { toFun := fun p =>
      ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_fst.comp continuous_subtype_val }

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
@[simp] theorem graphToDomainContinuousMap_apply
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphToDomainContinuousMap Stage sys ω i p =
      ⟨p.1.1, ⟨p.1.2, p.2⟩⟩ :=
  rfl

def graphToDomainCocone :
    Cocone (graphTopologicalDiagram Stage sys ω) where
  pt := TopCat.of (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalColimit
    Stage sys ω)
  ι := {
    app := fun i =>
      TopCat.ofHom (graphToDomainContinuousMap Stage sys ω i) ≫
        CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
          Stage sys ω i
    naturality := by
      intro i j f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      rw [TopCat.comp_app, TopCat.comp_app]
      change
        CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
            Stage sys ω j
            (graphToDomainContinuousMap Stage sys ω j
              (graphContinuousMap Stage sys ω (leOfHom f) p)) =
          CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
            Stage sys ω i (graphToDomainContinuousMap Stage sys ω i p)
      have hdomain :
          graphToDomainContinuousMap Stage sys ω j
              (graphContinuousMap Stage sys ω (leOfHom f) p) =
            filteredClosedTomitaDomainMap Stage sys ω (leOfHom f)
              (graphToDomainContinuousMap Stage sys ω i p) := by
        apply Subtype.ext
        change
          filteredGNSMap Stage sys ω (leOfHom f) p.1.1 =
            filteredGNSMap Stage sys ω (leOfHom f) p.1.1
        rfl
      rw [hdomain]
      exact
        topologicalInjection_transition Stage sys ω (leOfHom f)
          (graphToDomainContinuousMap Stage sys ω i p) }

noncomputable def graphToDomainTopologicalColimitMap :
    graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalColimit
        Stage sys ω) :=
  colimit.desc (graphTopologicalDiagram Stage sys ω)
    (graphToDomainCocone Stage sys ω)

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
@[simp] theorem graphToDomainTopologicalColimitMap_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphToDomainTopologicalColimitMap Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
        Stage sys ω i (graphToDomainContinuousMap Stage sys ω i p) := by
  have h := topologicalDirectDescend_stage
    (graphTopologicalDiagram Stage sys ω)
    (graphToDomainCocone Stage sys ω) i
  exact congrArg (fun f => f p) h

omit [Nonempty I] [IsDirectedOrder I] [DecidableEq I] in
theorem graphToDomainTopologicalColimitMap_unique
    (f : graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalColimit
        Stage sys ω))
    (h : ∀ (i : I) (p : graphCarrier Stage sys ω i),
      f (graphTopologicalInjection Stage sys ω i p) =
        CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
          Stage sys ω i (graphToDomainContinuousMap Stage sys ω i p)) :
    f = graphToDomainTopologicalColimitMap Stage sys ω := by
  apply topologicalDirectDescend_unique
    (graphTopologicalDiagram Stage sys ω)
    (graphToDomainCocone Stage sys ω) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change f (graphTopologicalInjection Stage sys ω i p) =
    CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
      Stage sys ω i (graphToDomainContinuousMap Stage sys ω i p)
  exact h i p

def domainStageToGlobalHilbertContinuousMap (i : I) :
    ContinuousMap (closedTomitaDomain (ω.state i))
      (GNSHilbertColimit Stage sys ω) :=
  { toFun := fun x =>
      gnsStageToHilbertColimit Stage sys ω i x.1
    continuous_toFun :=
      (gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i).continuous.comp
        continuous_subtype_val }

def domainToGlobalHilbertCocone :
    Cocone
      (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalDiagram
        Stage sys ω) where
  pt := TopCat.of (GNSHilbertColimit Stage sys ω)
  ι := {
    app := fun i =>
      TopCat.ofHom (domainStageToGlobalHilbertContinuousMap Stage sys ω i)
    naturality := by
      intro i j f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      rw [TopCat.comp_app]
      change
        gnsStageToHilbertColimit Stage sys ω j
            (filteredClosedTomitaDomainMap Stage sys ω (leOfHom f) x).1 =
          gnsStageToHilbertColimit Stage sys ω i x.1
      rw [filteredClosedTomitaDomainMap_apply]
      exact gnsStageToHilbertColimit_transition Stage sys ω
        (leOfHom f) x.1 }

noncomputable def domainTopologicalColimitToGlobalHilbert :
    CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalColimit
        Stage sys ω ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  colimit.desc
    (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalDiagram
      Stage sys ω)
    (domainToGlobalHilbertCocone Stage sys ω)

@[simp] theorem domainTopologicalColimitToGlobalHilbert_stage
    (i : I) (x : closedTomitaDomain (ω.state i)) :
    domainTopologicalColimitToGlobalHilbert Stage sys ω
        (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalInjection
          Stage sys ω i x) =
      gnsStageToHilbertColimit Stage sys ω i x.1 := by
  have h := topologicalDirectDescend_stage
    (CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit.topologicalDiagram
      Stage sys ω)
    (domainToGlobalHilbertCocone Stage sys ω) i
  exact congrArg (fun f => f x) h

abbrev globalGraphPair :=
  GNSHilbertColimit Stage sys ω × GNSHilbertColimit Stage sys ω

def graphStageToGlobalPair (i : I) :
    ContinuousMap (graphCarrier Stage sys ω i) (globalGraphPair Stage sys ω) :=
  { toFun := fun p =>
      (gnsStageToHilbertColimit Stage sys ω i p.1.1,
        gnsStageToHilbertColimit Stage sys ω i p.1.2)
    continuous_toFun := by
      exact
        ((gnsStageToHilbertColimitContinuousLinearMap
          Stage sys ω i).continuous.comp
          (continuous_fst.comp continuous_subtype_val)).prodMk
        ((gnsStageToHilbertColimitContinuousLinearMap
          Stage sys ω i).continuous.comp
          (continuous_snd.comp continuous_subtype_val)) }

def graphToGlobalPairCocone :
    Cocone (graphTopologicalDiagram Stage sys ω) where
  pt := TopCat.of (globalGraphPair Stage sys ω)
  ι := {
    app := fun i => TopCat.ofHom (graphStageToGlobalPair Stage sys ω i)
    naturality := by
      intro i j f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      change
        (gnsStageToHilbertColimit Stage sys ω j
            (filteredGNSPairMap Stage sys ω (leOfHom f) p.1).1,
          gnsStageToHilbertColimit Stage sys ω j
            (filteredGNSPairMap Stage sys ω (leOfHom f) p.1).2) =
        (gnsStageToHilbertColimit Stage sys ω i p.1.1,
          gnsStageToHilbertColimit Stage sys ω i p.1.2)
      apply Prod.ext
      · exact gnsStageToHilbertColimit_transition Stage sys ω
          (leOfHom f) p.1.1
      · exact gnsStageToHilbertColimit_transition Stage sys ω
          (leOfHom f) p.1.2 }

def graphSecondToGlobalHilbertContinuousMap (i : I) :
    ContinuousMap (graphCarrier Stage sys ω i)
      (GNSHilbertColimit Stage sys ω) :=
  { toFun := fun p => gnsStageToHilbertColimit Stage sys ω i p.1.2
    continuous_toFun :=
      (gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i).continuous.comp
        (continuous_snd.comp continuous_subtype_val) }

def graphSecondToGlobalHilbertCocone :
    Cocone (graphTopologicalDiagram Stage sys ω) where
  pt := TopCat.of (GNSHilbertColimit Stage sys ω)
  ι := {
    app := fun i =>
      TopCat.ofHom (graphSecondToGlobalHilbertContinuousMap Stage sys ω i)
    naturality := by
      intro i j f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      rw [TopCat.comp_app]
      change
        gnsStageToHilbertColimit Stage sys ω j
            (filteredGNSPairMap Stage sys ω (leOfHom f) p.1).2 =
          gnsStageToHilbertColimit Stage sys ω i p.1.2
      exact gnsStageToHilbertColimit_transition Stage sys ω
        (leOfHom f) p.1.2 }

noncomputable def graphTopologicalColimitToGlobalHilbertSecond :
    graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  colimit.desc (graphTopologicalDiagram Stage sys ω)
    (graphSecondToGlobalHilbertCocone Stage sys ω)

@[simp] theorem graphTopologicalColimitToGlobalHilbertSecond_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphTopologicalColimitToGlobalHilbertSecond Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      gnsStageToHilbertColimit Stage sys ω i p.1.2 := by
  have h := topologicalDirectDescend_stage
    (graphTopologicalDiagram Stage sys ω)
    (graphSecondToGlobalHilbertCocone Stage sys ω) i
  exact congrArg (fun f => f p) h

theorem graphTopologicalColimitToGlobalHilbertSecond_unique
    (f : graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω))
    (h : ∀ (i : I) (p : graphCarrier Stage sys ω i),
      f (graphTopologicalInjection Stage sys ω i p) =
        gnsStageToHilbertColimit Stage sys ω i p.1.2) :
    f = graphTopologicalColimitToGlobalHilbertSecond Stage sys ω := by
  apply topologicalDirectDescend_unique
    (graphTopologicalDiagram Stage sys ω)
    (graphSecondToGlobalHilbertCocone Stage sys ω) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change f (graphTopologicalInjection Stage sys ω i p) =
    gnsStageToHilbertColimit Stage sys ω i p.1.2
  exact h i p

def graphFirstToGlobalHilbertContinuousMap (i : I) :
    ContinuousMap (graphCarrier Stage sys ω i)
      (GNSHilbertColimit Stage sys ω) :=
  { toFun := fun p => gnsStageToHilbertColimit Stage sys ω i p.1.1
    continuous_toFun :=
      (gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i).continuous.comp
        (continuous_fst.comp continuous_subtype_val) }

def graphFirstToGlobalHilbertCocone :
    Cocone (graphTopologicalDiagram Stage sys ω) where
  pt := TopCat.of (GNSHilbertColimit Stage sys ω)
  ι := {
    app := fun i =>
      TopCat.ofHom (graphFirstToGlobalHilbertContinuousMap Stage sys ω i)
    naturality := by
      intro i j f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      rw [TopCat.comp_app]
      change
        gnsStageToHilbertColimit Stage sys ω j
            (filteredGNSPairMap Stage sys ω (leOfHom f) p.1).1 =
          gnsStageToHilbertColimit Stage sys ω i p.1.1
      exact gnsStageToHilbertColimit_transition Stage sys ω
        (leOfHom f) p.1.1 }

noncomputable def graphTopologicalColimitToGlobalHilbertFirst :
    graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  colimit.desc (graphTopologicalDiagram Stage sys ω)
    (graphFirstToGlobalHilbertCocone Stage sys ω)

@[simp] theorem graphTopologicalColimitToGlobalHilbertFirst_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphTopologicalColimitToGlobalHilbertFirst Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      gnsStageToHilbertColimit Stage sys ω i p.1.1 := by
  have h := topologicalDirectDescend_stage
    (graphTopologicalDiagram Stage sys ω)
    (graphFirstToGlobalHilbertCocone Stage sys ω) i
  exact congrArg (fun f => f p) h

theorem graphTopologicalColimitToGlobalHilbertFirst_unique
    (f : graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω))
    (h : ∀ (i : I) (p : graphCarrier Stage sys ω i),
      f (graphTopologicalInjection Stage sys ω i p) =
        gnsStageToHilbertColimit Stage sys ω i p.1.1) :
    f = graphTopologicalColimitToGlobalHilbertFirst Stage sys ω := by
  apply topologicalDirectDescend_unique
    (graphTopologicalDiagram Stage sys ω)
    (graphFirstToGlobalHilbertCocone Stage sys ω) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change f (graphTopologicalInjection Stage sys ω i p) =
    gnsStageToHilbertColimit Stage sys ω i p.1.1
  exact h i p

noncomputable def graphTopologicalColimitToGlobalPair :
    graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (globalGraphPair Stage sys ω) :=
  colimit.desc (graphTopologicalDiagram Stage sys ω)
    (graphToGlobalPairCocone Stage sys ω)

@[simp] theorem graphTopologicalColimitToGlobalPair_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphTopologicalColimitToGlobalPair Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      graphStageToGlobalPair Stage sys ω i p := by
  have h := topologicalDirectDescend_stage
    (graphTopologicalDiagram Stage sys ω)
    (graphToGlobalPairCocone Stage sys ω) i
  exact congrArg (fun f => f p) h

theorem graphTopologicalColimitToGlobalPair_unique
    (f : graphTopologicalColimit Stage sys ω ⟶
      TopCat.of (globalGraphPair Stage sys ω))
    (h : ∀ (i : I) (p : graphCarrier Stage sys ω i),
      f (graphTopologicalInjection Stage sys ω i p) =
        graphStageToGlobalPair Stage sys ω i p) :
    f = graphTopologicalColimitToGlobalPair Stage sys ω := by
  apply topologicalDirectDescend_unique
    (graphTopologicalDiagram Stage sys ω)
    (graphToGlobalPairCocone Stage sys ω) f
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change f (graphTopologicalInjection Stage sys ω i p) =
    graphStageToGlobalPair Stage sys ω i p
  exact h i p

def globalTomitaGraphClosure : Set (globalGraphPair Stage sys ω) :=
  closure (Set.range (graphTopologicalColimitToGlobalPair Stage sys ω))

theorem isClosed_globalTomitaGraphClosure :
    IsClosed (globalTomitaGraphClosure Stage sys ω) :=
  isClosed_closure

theorem graphTopologicalColimitToGlobalPair_mem_globalTomitaGraphClosure
    (x : graphTopologicalColimit Stage sys ω) :
    graphTopologicalColimitToGlobalPair Stage sys ω x ∈
      globalTomitaGraphClosure Stage sys ω := by
  exact subset_closure ⟨x, rfl⟩

theorem graphStageToGlobalPair_mem_globalTomitaGraphClosure
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphStageToGlobalPair Stage sys ω i p ∈
      globalTomitaGraphClosure Stage sys ω := by
  apply subset_closure
  refine ⟨graphTopologicalInjection Stage sys ω i p, ?_⟩
  exact graphTopologicalColimitToGlobalPair_stage Stage sys ω i p

def globalTomitaDomain : Set (GNSHilbertColimit Stage sys ω) :=
  {x | ∃ y, (x, y) ∈ globalTomitaGraphClosure Stage sys ω}

theorem graphTopologicalColimitToGlobalPair_fst_mem_globalTomitaDomain
    (x : graphTopologicalColimit Stage sys ω) :
    (graphTopologicalColimitToGlobalPair Stage sys ω x).1 ∈
      globalTomitaDomain Stage sys ω := by
  refine ⟨(graphTopologicalColimitToGlobalPair Stage sys ω x).2, ?_⟩
  exact graphTopologicalColimitToGlobalPair_mem_globalTomitaGraphClosure
    Stage sys ω x

theorem graphStageToGlobalPair_fst_mem_globalTomitaDomain
    (i : I) (p : graphCarrier Stage sys ω i) :
    (graphStageToGlobalPair Stage sys ω i p).1 ∈
      globalTomitaDomain Stage sys ω := by
  refine ⟨(graphStageToGlobalPair Stage sys ω i p).2, ?_⟩
  exact graphStageToGlobalPair_mem_globalTomitaGraphClosure
    Stage sys ω i p

abbrev globalTomitaGraphCarrier :=
  {p : globalGraphPair Stage sys ω //
    p ∈ globalTomitaGraphClosure Stage sys ω}

abbrev globalTomitaDomainCarrier :=
  {x : GNSHilbertColimit Stage sys ω //
    x ∈ globalTomitaDomain Stage sys ω}

def globalTomitaGraphCarrierToDomain :
    ContinuousMap (globalTomitaGraphCarrier Stage sys ω)
      (globalTomitaDomainCarrier Stage sys ω) :=
  { toFun := fun p =>
      ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_fst.comp continuous_subtype_val }

@[simp] theorem globalTomitaGraphCarrierToDomain_apply
    (p : globalTomitaGraphCarrier Stage sys ω) :
    globalTomitaGraphCarrierToDomain Stage sys ω p =
      ⟨p.1.1, ⟨p.1.2, p.2⟩⟩ :=
  rfl

def graphTopologicalColimitToGlobalGraphCarrier :
    ContinuousMap (graphTopologicalColimit Stage sys ω)
      (globalTomitaGraphCarrier Stage sys ω) :=
  { toFun := fun x =>
      ⟨graphTopologicalColimitToGlobalPair Stage sys ω x,
        graphTopologicalColimitToGlobalPair_mem_globalTomitaGraphClosure
          Stage sys ω x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (graphTopologicalColimitToGlobalPair Stage sys ω).hom.continuous_toFun }

@[simp] theorem graphTopologicalColimitToGlobalGraphCarrier_apply
    (x : graphTopologicalColimit Stage sys ω) :
    graphTopologicalColimitToGlobalGraphCarrier Stage sys ω x =
      ⟨graphTopologicalColimitToGlobalPair Stage sys ω x,
        graphTopologicalColimitToGlobalPair_mem_globalTomitaGraphClosure
          Stage sys ω x⟩ :=
  rfl

def graphTopologicalColimitToGlobalGraphCarrierTopCatHom :
    TopCat.of (graphTopologicalColimit Stage sys ω) ⟶
      TopCat.of (globalTomitaGraphCarrier Stage sys ω) :=
  TopCat.ofHom
    (graphTopologicalColimitToGlobalGraphCarrier Stage sys ω)

def globalTomitaGraphCarrierValTopCatHom :
    TopCat.of (globalTomitaGraphCarrier Stage sys ω) ⟶
      TopCat.of (globalGraphPair Stage sys ω) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem globalTomitaGraphCarrierValTopCatHom_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (globalTomitaGraphCarrierValTopCatHom Stage sys ω) := by
  simpa [globalTomitaGraphCarrierValTopCatHom, globalTomitaGraphCarrier] using
    (isClosed_globalTomitaGraphClosure Stage sys ω).isClosedEmbedding_subtypeVal

theorem globalTomitaGraphCarrierValTopCatHom_closed_range :
    IsClosed (Set.range (globalTomitaGraphCarrierValTopCatHom Stage sys ω)) := by
  exact (globalTomitaGraphCarrierValTopCatHom_isClosedEmbedding Stage sys ω).isClosed_range

@[simp] theorem graphTopologicalColimitToGlobalGraphCarrier_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphTopologicalColimitToGlobalGraphCarrier Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      ⟨graphStageToGlobalPair Stage sys ω i p,
        graphStageToGlobalPair_mem_globalTomitaGraphClosure
          Stage sys ω i p⟩ := by
  apply Subtype.ext
  change graphTopologicalColimitToGlobalPair Stage sys ω
      (graphTopologicalInjection Stage sys ω i p) =
    graphStageToGlobalPair Stage sys ω i p
  exact graphTopologicalColimitToGlobalPair_stage Stage sys ω i p

theorem graphTopologicalColimitToGlobalGraphCarrier_val_eq_pair :
    graphTopologicalColimitToGlobalGraphCarrierTopCatHom Stage sys ω ≫
        globalTomitaGraphCarrierValTopCatHom Stage sys ω =
      graphTopologicalColimitToGlobalPair Stage sys ω := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change
    (graphTopologicalColimitToGlobalGraphCarrier Stage sys ω
      (graphTopologicalInjection Stage sys ω i p)).1 =
      graphTopologicalColimitToGlobalPair Stage sys ω
        (graphTopologicalInjection Stage sys ω i p)
  rw [graphTopologicalColimitToGlobalGraphCarrier_stage]
  rw [graphTopologicalColimitToGlobalPair_stage]

def globalTomitaGraphCarrierToDomainTopCatHom :
    TopCat.of (globalTomitaGraphCarrier Stage sys ω) ⟶
      TopCat.of (globalTomitaDomainCarrier Stage sys ω) :=
  TopCat.ofHom (globalTomitaGraphCarrierToDomain Stage sys ω)

def graphTopologicalColimitToGlobalDomainCarrierTopCatHom :
    TopCat.of (graphTopologicalColimit Stage sys ω) ⟶
      TopCat.of (globalTomitaDomainCarrier Stage sys ω) :=
  graphTopologicalColimitToGlobalGraphCarrierTopCatHom Stage sys ω ≫
    globalTomitaGraphCarrierToDomainTopCatHom Stage sys ω

@[simp] theorem graphTopologicalColimitToGlobalDomainCarrier_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    graphTopologicalColimitToGlobalDomainCarrierTopCatHom Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      ⟨(graphStageToGlobalPair Stage sys ω i p).1,
        graphStageToGlobalPair_fst_mem_globalTomitaDomain
          Stage sys ω i p⟩ := by
  change globalTomitaGraphCarrierToDomain Stage sys ω
      (graphTopologicalColimitToGlobalGraphCarrier Stage sys ω
        (graphTopologicalInjection Stage sys ω i p)) =
    ⟨(graphStageToGlobalPair Stage sys ω i p).1,
      graphStageToGlobalPair_fst_mem_globalTomitaDomain
        Stage sys ω i p⟩
  apply Subtype.ext
  change (graphTopologicalColimitToGlobalPair Stage sys ω
      (graphTopologicalInjection Stage sys ω i p)).1 =
    (graphStageToGlobalPair Stage sys ω i p).1
  rw [graphTopologicalColimitToGlobalPair_stage]

def globalTomitaDomainCarrierValTopCatHom :
    TopCat.of (globalTomitaDomainCarrier Stage sys ω) ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def globalGraphPairFirstProjection :
    TopCat.of (globalGraphPair Stage sys ω) ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  TopCat.ofHom
    { toFun := Prod.fst
      continuous_toFun := continuous_fst }

theorem graphToGlobalDomainCarrier_val_eq_firstPairProjection :
    graphTopologicalColimitToGlobalDomainCarrierTopCatHom Stage sys ω ≫
        globalTomitaDomainCarrierValTopCatHom Stage sys ω =
      graphTopologicalColimitToGlobalPair Stage sys ω ≫
        globalGraphPairFirstProjection Stage sys ω := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  change
    (graphTopologicalColimitToGlobalDomainCarrierTopCatHom Stage sys ω
      (graphTopologicalInjection Stage sys ω i p)).1 =
      globalGraphPairFirstProjection Stage sys ω
        (graphTopologicalColimitToGlobalPair Stage sys ω
          (graphTopologicalInjection Stage sys ω i p))
  rw [graphTopologicalColimitToGlobalDomainCarrier_stage,
    graphTopologicalColimitToGlobalPair_stage]
  rfl

theorem graphToDomain_globalHilbert_eq_firstPairProjection :
    graphToDomainTopologicalColimitMap Stage sys ω ≫
        domainTopologicalColimitToGlobalHilbert Stage sys ω =
      graphTopologicalColimitToGlobalPair Stage sys ω ≫
        globalGraphPairFirstProjection Stage sys ω := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app, TopCat.comp_app]
  change
    domainTopologicalColimitToGlobalHilbert Stage sys ω
        (graphToDomainTopologicalColimitMap Stage sys ω
          (graphTopologicalInjection Stage sys ω i p)) =
      globalGraphPairFirstProjection Stage sys ω
        (graphTopologicalColimitToGlobalPair Stage sys ω
          (graphTopologicalInjection Stage sys ω i p))
  rw [graphToDomainTopologicalColimitMap_stage,
    domainTopologicalColimitToGlobalHilbert_stage,
    graphTopologicalColimitToGlobalPair_stage]
  rfl

theorem graphTopologicalColimitToGlobalHilbertFirst_eq_domain_route :
    graphTopologicalColimitToGlobalHilbertFirst Stage sys ω =
      graphToDomainTopologicalColimitMap Stage sys ω ≫
        domainTopologicalColimitToGlobalHilbert Stage sys ω := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change
    graphTopologicalColimitToGlobalHilbertFirst Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      (graphToDomainTopologicalColimitMap Stage sys ω ≫
        domainTopologicalColimitToGlobalHilbert Stage sys ω)
        (graphTopologicalInjection Stage sys ω i p)
  rw [TopCat.comp_app,
    graphTopologicalColimitToGlobalHilbertFirst_stage,
    graphToDomainTopologicalColimitMap_stage,
    domainTopologicalColimitToGlobalHilbert_stage]
  rfl

def globalGraphPairSecondProjection :
    TopCat.of (globalGraphPair Stage sys ω) ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  TopCat.ofHom
    { toFun := Prod.snd
      continuous_toFun := continuous_snd }

@[simp] theorem graphTopologicalColimitToGlobalPair_second_stage
    (i : I) (p : graphCarrier Stage sys ω i) :
    (graphTopologicalColimitToGlobalPair Stage sys ω ≫
      globalGraphPairSecondProjection Stage sys ω)
        (graphTopologicalInjection Stage sys ω i p) =
      gnsStageToHilbertColimit Stage sys ω i p.1.2 := by
  rw [TopCat.comp_app, graphTopologicalColimitToGlobalPair_stage]
  rfl

theorem graphTopologicalColimitToGlobalHilbertSecond_eq_pairSecondProjection :
    graphTopologicalColimitToGlobalHilbertSecond Stage sys ω =
      graphTopologicalColimitToGlobalPair Stage sys ω ≫
        globalGraphPairSecondProjection Stage sys ω := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change
    graphTopologicalColimitToGlobalHilbertSecond Stage sys ω
        (graphTopologicalInjection Stage sys ω i p) =
      (graphTopologicalColimitToGlobalPair Stage sys ω ≫
        globalGraphPairSecondProjection Stage sys ω)
        (graphTopologicalInjection Stage sys ω i p)
  rw [TopCat.comp_app,
    graphTopologicalColimitToGlobalHilbertSecond_stage,
    graphTopologicalColimitToGlobalPair_stage]
  rfl

end CStarStateColimit.Native.FilteredGNSTomitaGraphTopologicalColimit
