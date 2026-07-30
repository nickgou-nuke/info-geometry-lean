import InfoGeometry.Canonical.FilteredGNSCofinalTail
import InfoGeometry.Canonical.FilteredGNSHilbertColimitTopology
import InfoGeometry.Canonical.FilteredGNSCofinalTailTopCatEquivalence
import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentationTransport
import InfoGeometry.Canonical.FilteredGNSTailRepresentationTopology

/-!
# TopCat realization of a cofinal filtered GNS tail

The algebraic/completed cofinal-tail owner constructs the canonical map from a
tail Hilbert colimit to the global Hilbert colimit.  This file records the
parallel `TopCat` colimit cocone and proves that its universal map has dense
range.  The result is deliberately only a density statement: no embedding of
a general `TopCat` colimit injection is assumed.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSCofinalTailTopological

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
open CStarStateColimit.Native.FilteredGNSCofinalTail
open CStarStateColimit.Native.FilteredGNSCofinalTailTopology
open CStarStateColimit.Native.FilteredGNSCofinalTailTopCatEquivalence
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentationTransport
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailRepresentationTopology
open CategoryTheory CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

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

/-! A star algebra homomorphism between C*-algebras is contractive.  Turning
that native norm inequality into `IsBoundedLinearMap` supplies the missing
topological readout without adding a separate continuity axiom. -/
theorem continuous_starAlgHom
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (π : A →⋆ₐ[ℂ] B) : Continuous π := by
  have hlin : IsLinearMap ℂ π :=
    IsLinearMap.mk (fun x y => map_add π x y) (fun c x => map_smul π c x)
  have hb : IsBoundedLinearMap ℂ π := hlin.with_bound 1 (by
    intro x
    have h := NonUnitalStarAlgHom.nnnorm_apply_le π x
    have h' : (‖π x‖₊ : ℝ) ≤ (‖x‖₊ : ℝ) :=
      NNReal.coe_le_coe.mpr h
    simpa using h')
  exact hb.continuous

def upperIndexInclusion (i₀ : I) : UpperIndex i₀ ⥤ I where
  obj j := j.1
  map f := homOfLE (leOfHom f)
  map_id := by
    intro j
    apply Subsingleton.elim
  map_comp := by
    intro j k l f g
    apply Subsingleton.elim

abbrev upperGnsTopologicalDiagram (i₀ : I) :
    UpperIndex i₀ ⥤ TopCat.{u} :=
  upperIndexInclusion i₀ ⋙ gnsTopologicalDiagram Stage sys ω

def upperGnsTopologicalCocone (i₀ : I) :
    Cocone (upperGnsTopologicalDiagram Stage sys ω i₀) :=
  Cocone.whisker (upperIndexInclusion i₀)
    (gnsTopologicalCocone Stage sys ω)

abbrev upperGnsTopologicalColimit (i₀ : I) : TopCat.{u} :=
  topologicalDirectColimit (upperGnsTopologicalDiagram Stage sys ω i₀)

noncomputable def upperGnsTopologicalColimitToHilbert (i₀ : I) :
    upperGnsTopologicalColimit Stage sys ω i₀ ⟶
      (upperGnsTopologicalCocone Stage sys ω i₀).pt :=
  topologicalDirectDescend
    (upperGnsTopologicalDiagram Stage sys ω i₀)
    (upperGnsTopologicalCocone Stage sys ω i₀)

@[reassoc]
theorem upperGnsTopologicalColimitToHilbert_stage
    (i₀ : I) (j : UpperIndex i₀) :
    topologicalDirectInjection
        (upperGnsTopologicalDiagram Stage sys ω i₀) j ≫
      upperGnsTopologicalColimitToHilbert Stage sys ω i₀ =
      (upperGnsTopologicalCocone Stage sys ω i₀).ι.app j := by
  exact topologicalDirectDescend_stage
    (upperGnsTopologicalDiagram Stage sys ω i₀)
    (upperGnsTopologicalCocone Stage sys ω i₀) j

/-- The topological colimit of every upper GNS tail maps densely into the
global completed Hilbert colimit. -/
theorem denseRange_upperGnsTopologicalColimitToHilbert (i₀ : I) :
    DenseRange (upperGnsTopologicalColimitToHilbert Stage sys ω i₀) := by
  apply (dense_iUnion_range_upper_gnsStageToHilbertColimit
    Stage sys ω i₀).mono
  rintro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, ⟨y, rfl⟩⟩ := hx
  refine ⟨topologicalDirectInjection
      (upperGnsTopologicalDiagram Stage sys ω i₀) j y, ?_⟩
  have h := congrArg (fun f => f y)
    (upperGnsTopologicalColimitToHilbert_stage Stage sys ω i₀ j)
  exact h

/-! The same upper-stage diagram also has its canonical cocone into the
completed tail Hilbert colimit.  This is the comparison leg used below. -/
def upperGnsToTailHilbertCocone (i₀ : I) :
    Cocone (upperGnsTopologicalDiagram Stage sys ω i₀) where
  pt := TopCat.of
    (HilbertDirectLimit
      (TailGNSStage Stage sys ω i₀)
      (tailGNSIsometricDirectSystem Stage sys ω i₀))
  ι :=
    { app := fun j => TopCat.ofHom
        { toFun := stageToHilbertDirectLimit
            (TailGNSStage Stage sys ω i₀)
            (tailGNSIsometricDirectSystem Stage sys ω i₀) j
          continuous_toFun :=
            (stageToHilbertDirectLimit
              (TailGNSStage Stage sys ω i₀)
              (tailGNSIsometricDirectSystem Stage sys ω i₀) j).continuous }
      naturality := by
        intro j k f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact stageToHilbertDirectLimit_transition
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)
          (leOfHom f) x
    }

noncomputable def upperGnsToTailHilbertColimitMap (i₀ : I) :
    upperGnsTopologicalColimit Stage sys ω i₀ ⟶
      (upperGnsToTailHilbertCocone Stage sys ω i₀).pt :=
  topologicalDirectDescend
    (upperGnsTopologicalDiagram Stage sys ω i₀)
    (upperGnsToTailHilbertCocone Stage sys ω i₀)

omit [Nonempty I] in
@[reassoc]
theorem upperGnsToTailHilbertColimitMap_stage
    (i₀ : I) (j : UpperIndex i₀) :
    topologicalDirectInjection
        (upperGnsTopologicalDiagram Stage sys ω i₀) j ≫
      upperGnsToTailHilbertColimitMap Stage sys ω i₀ =
      (upperGnsToTailHilbertCocone Stage sys ω i₀).ι.app j := by
  exact topologicalDirectDescend_stage
    (upperGnsTopologicalDiagram Stage sys ω i₀)
    (upperGnsToTailHilbertCocone Stage sys ω i₀) j

theorem upperGnsTopologicalColimitToHilbert_eq_tail_comparison
    (i₀ : I) :
    upperGnsTopologicalColimitToHilbert Stage sys ω i₀ =
      upperGnsToTailHilbertColimitMap Stage sys ω i₀ ≫
        tailToGlobalTopCatMap Stage sys ω i₀ := by
  symm
  apply topologicalDirectDescend_unique
    (upperGnsTopologicalDiagram Stage sys ω i₀)
    (upperGnsTopologicalCocone Stage sys ω i₀)
  intro j
  rw [← Category.assoc,
    upperGnsToTailHilbertColimitMap_stage]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact tailHilbertGlobalHomeomorph_stage Stage sys ω i₀ j x

/-- The transported global stage representation, exposed as a continuous
`TopCat` endomorphism of the global Hilbert colimit. -/
def globalStageRepresentationTopCatHom
    {i₀ : I} (a : Stage i₀) :
    TopCat.of (GNSHilbertColimit Stage sys ω) ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  TopCat.ofHom
    { toFun := globalStageRepresentationStarAlgHom Stage sys ω i₀ a
      continuous_toFun :=
        globalStageRepresentation_continuous_apply Stage sys ω a }

@[simp] theorem globalStageRepresentationTopCatHom_apply
    {i₀ : I} (a : Stage i₀) (x : GNSHilbertColimit Stage sys ω) :
    globalStageRepresentationTopCatHom Stage sys ω a x =
      globalStageRepresentationStarAlgHom Stage sys ω i₀ a x :=
  rfl

/-- The bundled global `StarAlgHom` itself is exposed as a continuous
operator-valued readout. -/
def globalStageRepresentationContinuousMap
    {i₀ : I} :
    ContinuousMap (Stage i₀)
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) :=
  { toFun := globalStageRepresentationStarAlgHom Stage sys ω i₀
    continuous_toFun := by
      have hcont : Continuous
          (globalStageRepresentationStarAlgHom Stage sys ω i₀) :=
        continuous_starAlgHom
          (A := Stage i₀)
          (B := GNSHilbertColimit Stage sys ω →L[ℂ]
            GNSHilbertColimit Stage sys ω)
          (globalStageRepresentationStarAlgHom Stage sys ω i₀)
      exact hcont }

@[simp] theorem globalStageRepresentationContinuousMap_apply
    {i₀ : I} (a : Stage i₀) :
    globalStageRepresentationContinuousMap Stage sys ω a =
      globalStageRepresentationStarAlgHom Stage sys ω i₀ a := by
  simp only [globalStageRepresentationContinuousMap, ContinuousMap.coe_mk]

/-- The tail/global representation intertwining law as an equality of
continuous `TopCat` maps. -/
theorem globalStageRepresentationTopCatHom_intertwines
    {i₀ : I} (a : Stage i₀) :
    tailToGlobalTopCatMap Stage sys ω i₀ ≫
        globalStageRepresentationTopCatHom Stage sys ω a =
      tailCompletedRepresentationTopCatHom Stage sys ω a ≫
        tailToGlobalTopCatMap Stage sys ω i₀ := by
  apply TopCat.hom_ext
  ext x
  have h := congrArg (fun f => f x)
    (globalStageRepresentation_intertwines Stage sys ω a)
  simpa only [tailToGlobalTopCatMap, globalStageRepresentationTopCatHom,
    tailCompletedRepresentationTopCatHom, TopCat.comp_app,
    ContinuousLinearMap.comp_apply] using h

/-! Stagewise GNS operators form a natural endomorphism of the upper-tail
`TopCat` diagram.  Its colimit map can therefore be compared directly with
the transported global representation. -/
def upperTailRepresentationNatTrans
    {i₀ : I} (a : Stage i₀) :
    upperGnsTopologicalDiagram Stage sys ω i₀ ⟶
      upperGnsTopologicalDiagram Stage sys ω i₀ where
  app j := tailGNSOperatorTopCatHom Stage sys ω a j
  naturality := by
    intro j k f
    exact tailGNSOperatorTopCatHom_intertwines Stage sys ω a (leOfHom f)

noncomputable def upperTailRepresentationColimitMap
    {i₀ : I} (a : Stage i₀) :
    upperGnsTopologicalColimit Stage sys ω i₀ ⟶
      upperGnsTopologicalColimit Stage sys ω i₀ :=
  colim.map (upperTailRepresentationNatTrans Stage sys ω a)

theorem upperTailRepresentationColimitMap_stage
    {i₀ : I} (a : Stage i₀) (j : UpperIndex i₀) :
    topologicalDirectInjection
        (upperGnsTopologicalDiagram Stage sys ω i₀) j ≫
      upperTailRepresentationColimitMap Stage sys ω a =
      (upperTailRepresentationNatTrans Stage sys ω a).app j ≫
        topologicalDirectInjection
          (upperGnsTopologicalDiagram Stage sys ω i₀) j := by
  exact colimit.ι_map (upperTailRepresentationNatTrans Stage sys ω a) j

theorem upperTailRepresentation_stage_global_intertwines
    {i₀ : I} (a : Stage i₀) (j : UpperIndex i₀) :
    (upperTailRepresentationNatTrans Stage sys ω a).app j ≫
        (upperGnsTopologicalCocone Stage sys ω i₀).ι.app j =
      (upperGnsTopologicalCocone Stage sys ω i₀).ι.app j ≫
        globalStageRepresentationTopCatHom Stage sys ω a := by
  apply TopCat.hom_ext
  ext x
  exact (globalStageRepresentation_stage Stage sys ω a j x).symm

/-- The stagewise representation colimit intertwines with the global
representation after passage through the dense topological colimit map. -/
theorem upperTailRepresentationColimitMap_intertwines_global
    {i₀ : I} (a : Stage i₀) :
    upperTailRepresentationColimitMap Stage sys ω a ≫
        upperGnsTopologicalColimitToHilbert Stage sys ω i₀ =
      upperGnsTopologicalColimitToHilbert Stage sys ω i₀ ≫
        globalStageRepresentationTopCatHom Stage sys ω a := by
  apply colimit.hom_ext
  intro j
  calc
    topologicalDirectInjection
          (upperGnsTopologicalDiagram Stage sys ω i₀) j ≫
        (upperTailRepresentationColimitMap Stage sys ω a ≫
          upperGnsTopologicalColimitToHilbert Stage sys ω i₀) =
        (topologicalDirectInjection
          (upperGnsTopologicalDiagram Stage sys ω i₀) j ≫
          upperTailRepresentationColimitMap Stage sys ω a) ≫
          upperGnsTopologicalColimitToHilbert Stage sys ω i₀ :=
      (Category.assoc _ _ _).symm
    _ = ((upperTailRepresentationNatTrans Stage sys ω a).app j ≫
          topologicalDirectInjection
            (upperGnsTopologicalDiagram Stage sys ω i₀) j) ≫
          upperGnsTopologicalColimitToHilbert Stage sys ω i₀ := by
      rw [upperTailRepresentationColimitMap_stage]
    _ = (upperTailRepresentationNatTrans Stage sys ω a).app j ≫
          ((upperGnsTopologicalCocone Stage sys ω i₀).ι.app j) := by
      rw [Category.assoc,
        upperGnsTopologicalColimitToHilbert_stage]
    _ = (upperGnsTopologicalCocone Stage sys ω i₀).ι.app j ≫
          globalStageRepresentationTopCatHom Stage sys ω a :=
      upperTailRepresentation_stage_global_intertwines Stage sys ω a j
    _ = topologicalDirectInjection
          (upperGnsTopologicalDiagram Stage sys ω i₀) j ≫
          (upperGnsTopologicalColimitToHilbert Stage sys ω i₀ ≫
            globalStageRepresentationTopCatHom Stage sys ω a) := by
      rw [← upperGnsTopologicalColimitToHilbert_stage,
        ← Category.assoc]

/-- The topological global readout retains the involution supplied by its
bundled `StarAlgHom`. -/
theorem globalStageRepresentationStarAlgHom_map_star
    {i₀ : I} (a : Stage i₀) :
    globalStageRepresentationStarAlgHom Stage sys ω i₀ (star a) =
      star (globalStageRepresentationStarAlgHom Stage sys ω i₀ a) := by
  exact StarHomClass.map_star
    (globalStageRepresentationStarAlgHom Stage sys ω i₀) a

@[simp] theorem globalStageRepresentationTopCatHom_star_apply
    {i₀ : I} (a : Stage i₀) (x : GNSHilbertColimit Stage sys ω) :
    globalStageRepresentationTopCatHom Stage sys ω (star a) x =
      star (globalStageRepresentationStarAlgHom Stage sys ω i₀ a) x := by
  rw [globalStageRepresentationTopCatHom_apply,
    globalStageRepresentationStarAlgHom_map_star]

@[simp] theorem tailCompletedRepresentationTopCatHom_star_apply
    {i₀ : I} (a : Stage i₀)
    (x : HilbertDirectLimit
      (TailGNSStage Stage sys ω i₀)
      (tailGNSIsometricDirectSystem Stage sys ω i₀)) :
    tailCompletedRepresentationTopCatHom Stage sys ω (star a) x =
      star (tailCompletedRepresentation Stage sys ω a) x := by
  rw [tailCompletedRepresentationTopCatHom_apply,
    tailCompletedRepresentation_star]

def tailCompletedRepresentationContinuousMap
    {i₀ : I} :
    ContinuousMap (Stage i₀)
      (HilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀) →L[ℂ]
        HilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)) :=
  { toFun := tailCompletedRepresentationStarAlgHom Stage sys ω i₀
    continuous_toFun := by
      have hcont : Continuous
          (tailCompletedRepresentationStarAlgHom Stage sys ω i₀) :=
        continuous_starAlgHom
          (A := Stage i₀)
          (B := HilbertDirectLimit
            (TailGNSStage Stage sys ω i₀)
            (tailGNSIsometricDirectSystem Stage sys ω i₀) →L[ℂ]
            HilbertDirectLimit
              (TailGNSStage Stage sys ω i₀)
              (tailGNSIsometricDirectSystem Stage sys ω i₀))
          (tailCompletedRepresentationStarAlgHom Stage sys ω i₀)
      exact hcont }

@[simp] theorem tailCompletedRepresentationContinuousMap_apply
    {i₀ : I} (a : Stage i₀) :
    tailCompletedRepresentationContinuousMap Stage sys ω a =
      tailCompletedRepresentationStarAlgHom Stage sys ω i₀ a := by
  simp only [tailCompletedRepresentationContinuousMap, ContinuousMap.coe_mk]

/-- Unitary operator conjugation is a topological homeomorphism and preserves
the operator involution because it is induced by a `StarAlgEquiv`. -/
@[simp] theorem globalStageOperatorConjugationHomeomorph_star
    {i₀ : I}
    (T : HilbertDirectLimit
      (TailGNSStage Stage sys ω i₀)
      (tailGNSIsometricDirectSystem Stage sys ω i₀) →L[ℂ]
      HilbertDirectLimit
        (TailGNSStage Stage sys ω i₀)
        (tailGNSIsometricDirectSystem Stage sys ω i₀)) :
    globalStageOperatorConjugationHomeomorph Stage sys ω i₀ (star T) =
      star (globalStageOperatorConjugationHomeomorph Stage sys ω i₀ T) := by
  rw [globalStageOperatorConjugationHomeomorph_apply,
    globalStageOperatorConjugationHomeomorph_apply]
  exact StarHomClass.map_star
    ((tailHilbertGlobalEquiv Stage sys ω i₀).conjStarAlgEquiv) T

end CStarStateColimit.Native.FilteredGNSCofinalTailTopological
