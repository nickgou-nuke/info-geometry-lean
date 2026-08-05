import InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Filtered naturality of the q-CCR parameter topology

For a continuous star-inductive system, the transition maps act on all three
entries of `(c, (cstar, q))`.  This owner proves that the residual map commutes
with those transitions and therefore carries every closed q-CCR fiber to the
corresponding later-stage fiber.  It is the topological diagram needed before
forming a colimit of the relation loci.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

/-- Transition of the three-parameter q-CCR space. -/
def qCcrParameterTransitionMap
    {i j : I} (hij : i ≤ j) :
    ContinuousMap
      (QCCRParameterSpace (Stage i))
      (QCCRParameterSpace (Stage j)) :=
  { toFun := fun p =>
      (sys.map hij p.1,
        (sys.map hij p.2.1, sys.map hij p.2.2))
    continuous_toFun := by
      let f := sys.transitionCLM Stage hij
      exact (f.continuous.comp continuous_fst).prodMk
        ((f.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
          (f.continuous.comp (continuous_snd.comp continuous_snd))) }

@[simp] theorem qCcrParameterTransitionMap_apply
    {i j : I} (hij : i ≤ j)
    (c cstar q : Stage i) :
    qCcrParameterTransitionMap Stage sys hij (c, (cstar, q)) =
      (sys.map hij c, (sys.map hij cstar, sys.map hij q)) :=
  rfl

/-- Fixed-`q` specialization is natural for the parameter transition maps.

The parameter itself is transported by the same star-algebra map as the two
operator entries; this is the stagewise square used by the q-fiber colimit. -/
theorem qCcrSpecialization_parameterTransition_natural
    {i j : I} (hij : i ≤ j) (q : Stage i) (p : Stage i × Stage i) :
    qCcrParameterTransitionMap Stage sys hij
        (qCcrSpecializationMap (A := Stage i) q p) =
      qCcrSpecializationMap (A := Stage j) (sys.map hij q)
        (sys.map hij p.1, sys.map hij p.2) := by
  rfl

/- The transition on the two operator entries, used on the lower side of the
   specialization square. -/
def qCcrOperatorPairTransitionMap
    {i j : I} (hij : i ≤ j) :
    ContinuousMap (Stage i × Stage i) (Stage j × Stage j) :=
  { toFun := fun p => (sys.map hij p.1, sys.map hij p.2)
    continuous_toFun := by
      let f := sys.transitionCLM Stage hij
      exact (f.continuous.comp continuous_fst).prodMk
        (f.continuous.comp continuous_snd) }

/- The same square as an equality of `TopCat` morphisms. -/
theorem qCcrSpecialization_parameterTransition_topCat_natural
    {i j : I} (hij : i ≤ j) (q : Stage i) :
    TopCat.ofHom (qCcrSpecializationMap (A := Stage i) q) ≫
        TopCat.ofHom (qCcrParameterTransitionMap Stage sys hij) =
      TopCat.ofHom (qCcrOperatorPairTransitionMap Stage sys hij) ≫
        TopCat.ofHom (qCcrSpecializationMap (A := Stage j) (sys.map hij q)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact qCcrSpecialization_parameterTransition_natural Stage sys hij q p

/-- The full q-CCR parameter spaces form the ambient filtered `TopCat` diagram. -/
def qCcrParameterTopologicalDiagram : I ⥤ TopCat where
  obj i := TopCat.of (QCCRParameterSpace (Stage i))
  map f := TopCat.ofHom (qCcrParameterTransitionMap Stage sys (leOfHom f))
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rcases p with ⟨c, cstar, q⟩
    simp [qCcrParameterTransitionMap, sys.map_id]
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rcases p with ⟨c, cstar, q⟩
    dsimp [qCcrParameterTransitionMap]
    apply Prod.ext
    · exact congrArg (fun e => e c)
        (sys.map_comp (leOfHom f) (leOfHom g)).symm
    · apply Prod.ext
      · exact congrArg (fun e => e cstar)
          (sys.map_comp (leOfHom f) (leOfHom g)).symm
      · exact congrArg (fun e => e q)
          (sys.map_comp (leOfHom f) (leOfHom g)).symm

abbrev qCcrParameterTopologicalColimit : TopCat :=
  colimit (qCcrParameterTopologicalDiagram Stage sys)

def qCcrParameterTopologicalInjection (i : I) :
    (qCcrParameterTopologicalDiagram Stage sys).obj i ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  colimit.ι (qCcrParameterTopologicalDiagram Stage sys) i

theorem qCcrParameterTopologicalInjection_transition
    {i j : I} (hij : i ≤ j)
    (p : QCCRParameterSpace (Stage i)) :
    qCcrParameterTopologicalInjection Stage sys j
        (qCcrParameterTransitionMap Stage sys hij p) =
      qCcrParameterTopologicalInjection Stage sys i p := by
  have h :=
    (CategoryTheory.Limits.colimit.cocone
      (qCcrParameterTopologicalDiagram Stage sys)).w
      (CategoryTheory.homOfLE hij)
  simpa [qCcrParameterTopologicalInjection,
    qCcrParameterTopologicalDiagram] using congrArg (fun f => f p) h

/-- The q-CCR residual is natural for every star-algebra transition. -/
theorem qCcrParameterResidual_natural
    {i j : I} (hij : i ≤ j)
    (p : QCCRParameterSpace (Stage i)) :
    qCcrParameterResidualContinuousMap
        (A := Stage j) (qCcrParameterTransitionMap Stage sys hij p) =
      sys.map hij
        (qCcrParameterResidualContinuousMap (A := Stage i) p) := by
  change qCcrRelation (sys.map hij p.1)
      (sys.map hij p.2.1) (sys.map hij p.2.2) =
    sys.map hij (qCcrRelation p.1 p.2.1 p.2.2)
  simp [qCcrRelation]

/-- Transition of a fixed-q residual zero-locus. -/
def qCcrZeroLocusTransitionMap
    {i j : I} (hij : i ≤ j) (q : Stage i) :
    {p : Stage i × Stage i //
        p ∈ qCcrZeroLocus (A := Stage i) q} →
      {p : Stage j × Stage j //
        p ∈ qCcrZeroLocus (A := Stage j) (sys.map hij q)} :=
  fun p =>
    ⟨qCcrOperatorPairTransitionMap Stage sys hij p.1, by
      change qCcrParameterResidualContinuousMap (A := Stage j)
        (qCcrParameterTransitionMap Stage sys hij
          (qCcrSpecializationMap (A := Stage i) q p.1)) = 0
      simpa [qCcrParameterResidualContinuousMap, qCcrSpecializationMap,
        qCcrParameterTransitionMap, qCcrRelation] using
        congrArg (sys.map hij)
          (show qCcrRelation p.1.1 p.1.2 q = 0 from p.2)⟩

theorem continuous_qCcrZeroLocusTransitionMap
    {i j : I} (hij : i ≤ j) (q : Stage i) :
    Continuous (qCcrZeroLocusTransitionMap Stage sys hij q) := by
  apply Continuous.subtype_mk
  exact (qCcrOperatorPairTransitionMap Stage sys hij).continuous_toFun.comp
    continuous_subtype_val

def qCcrZeroLocusTransitionTopCatHom
    {i j : I} (hij : i ≤ j) (q : Stage i) :
    TopCat.of {p : Stage i × Stage i //
        p ∈ qCcrZeroLocus (A := Stage i) q} ⟶
      TopCat.of {p : Stage j × Stage j //
        p ∈ qCcrZeroLocus (A := Stage j) (sys.map hij q)} :=
  TopCat.ofHom
    { toFun := qCcrZeroLocusTransitionMap Stage sys hij q
      continuous_toFun := continuous_qCcrZeroLocusTransitionMap Stage sys hij q }

/-- The residual square as an equality in `TopCat`. -/
theorem qCcrParameterResidual_topCat_natural
    {i j : I} (hij : i ≤ j) :
    TopCat.ofHom (qCcrParameterTransitionMap Stage sys hij) ≫
        TopCat.ofHom (qCcrParameterResidualContinuousMap (A := Stage j)) =
      TopCat.ofHom (qCcrParameterResidualContinuousMap (A := Stage i)) ≫
        TopCat.ofHom (sys.transitionCLM Stage hij) := by
  apply TopCat.hom_ext
  ext p
  change qCcrParameterResidualContinuousMap
      (A := Stage j) (qCcrParameterTransitionMap Stage sys hij p) =
    sys.transitionCLM Stage hij
      (qCcrParameterResidualContinuousMap (A := Stage i) p)
  rw [ContinuousStarInductiveSystem.transitionCLM_apply]
  exact qCcrParameterResidual_natural Stage sys hij p

/-- Transition of the closed q-CCR zero fibers. -/
def qCcrParameterZeroFiberTransitionMap
    {i j : I} (hij : i ≤ j) :
    {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)} →
      {p : QCCRParameterSpace (Stage j) //
        p ∈ qCcrParameterZeroLocus (A := Stage j)} :=
  fun p =>
    ⟨qCcrParameterTransitionMap Stage sys hij p.1, by
      change qCcrParameterResidualContinuousMap
          (A := Stage j) (qCcrParameterTransitionMap Stage sys hij p.1) = 0
      rw [qCcrParameterResidual_natural Stage sys hij p.1]
      rw [p.2]
      exact map_zero _⟩

theorem continuous_qCcrParameterZeroFiberTransitionMap
    {i j : I} (hij : i ≤ j) :
    Continuous (qCcrParameterZeroFiberTransitionMap Stage sys hij) := by
  apply Continuous.subtype_mk
  exact (qCcrParameterTransitionMap Stage sys hij).continuous.comp
    continuous_subtype_val

def qCcrParameterZeroFiberTransitionTopCatHom
    {i j : I} (hij : i ≤ j) :
    TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)} ⟶
      TopCat.of {p : QCCRParameterSpace (Stage j) //
        p ∈ qCcrParameterZeroLocus (A := Stage j)} :=
  TopCat.ofHom
    { toFun := qCcrParameterZeroFiberTransitionMap Stage sys hij
      continuous_toFun :=
        continuous_qCcrParameterZeroFiberTransitionMap Stage sys hij }

/-- Forget the fixed-q witness and include a fiber point in the ambient
    residual zero-locus. -/
def qCcrParameterZeroLocusFiberInclusionTopCatHom (i : I) (q : Stage i) :
    TopCat.of
        (InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat.qCcrParameterZeroLocusFiberType
          (A := Stage i) q) ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)} :=
  TopCat.ofHom
    { toFun := fun p => ⟨p.1, p.2.1⟩
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun p => p.2.1) }

theorem qCcrSpecializationZeroLocus_transition_ambient_natural
    {i j : I} (hij : i ≤ j) (q : Stage i) :
    qCcrSpecializationZeroLocusTopCatHom (A := Stage i) q ≫
        qCcrParameterZeroLocusFiberInclusionTopCatHom (Stage := Stage) i q ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      qCcrZeroLocusTransitionTopCatHom Stage sys hij q ≫
        qCcrSpecializationZeroLocusTopCatHom (A := Stage j) (sys.map hij q) ≫
        qCcrParameterZeroLocusFiberInclusionTopCatHom (Stage := Stage) j
          (sys.map hij q) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

@[simp] theorem qCcrParameterZeroFiberTransitionTopCatHom_apply
    {i j : I} (hij : i ≤ j)
    (p : {p : QCCRParameterSpace (Stage i) //
      p ∈ qCcrParameterZeroLocus (A := Stage i)}) :
    qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij p =
      qCcrParameterZeroFiberTransitionMap Stage sys hij p :=
  rfl

/-- The closed q-CCR fibers form a genuine filtered `TopCat` diagram. -/
def qCcrParameterZeroFiberTopologicalDiagram : I ⥤ TopCat where
  obj i := TopCat.of
    {p : QCCRParameterSpace (Stage i) //
      p ∈ qCcrParameterZeroLocus (A := Stage i)}
  map f := qCcrParameterZeroFiberTransitionTopCatHom
    Stage sys (leOfHom f)
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    rcases p.1 with ⟨c, cstar, q⟩
    simp [qCcrParameterZeroFiberTransitionTopCatHom,
      qCcrParameterZeroFiberTransitionMap,
      qCcrParameterTransitionMap, sys.map_id]
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    dsimp [qCcrParameterZeroFiberTransitionTopCatHom,
      qCcrParameterZeroFiberTransitionMap]
    change qCcrParameterTransitionMap Stage sys
        (le_trans (leOfHom f) (leOfHom g)) p.1 =
      qCcrParameterTransitionMap Stage sys (leOfHom g)
        (qCcrParameterTransitionMap Stage sys (leOfHom f) p.1)
    dsimp [qCcrParameterTransitionMap]
    have hcomp := (sys.map_comp (leOfHom f) (leOfHom g)).symm
    apply Prod.ext
    · exact congrArg (fun e => e p.1.1) hcomp
    · apply Prod.ext
      · exact congrArg (fun e => e p.1.2.1) hcomp
      · exact congrArg (fun e => e p.1.2.2) hcomp

/-- Inclusion of each closed relation fiber into its ambient parameter space. -/
def qCcrParameterZeroFiberToParameterNatTrans :
    qCcrParameterZeroFiberTopologicalDiagram Stage sys ⟶
      qCcrParameterTopologicalDiagram Stage sys where
  app i := TopCat.ofHom
    { toFun := fun p => p.1
      continuous_toFun := continuous_subtype_val }
  naturality := by
    intro i j f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rfl

theorem qCcrParameterZeroFiberToParameterNatTrans_app_isClosedEmbedding
    (i : I) :
    Topology.IsClosedEmbedding
      ((qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i) := by
  simpa [qCcrParameterZeroFiberToParameterNatTrans] using
    (qCcrParameterZeroLocus_closed (A := Stage i)).isClosedEmbedding_subtypeVal

theorem qCcrParameterZeroFiberToParameterNatTrans_app_closed_range
    (i : I) :
    IsClosed (Set.range
      ((qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i)) := by
  exact (qCcrParameterZeroFiberToParameterNatTrans_app_isClosedEmbedding
    Stage sys i).isClosed_range

abbrev qCcrParameterZeroFiberTopologicalColimit : TopCat :=
  colimit (qCcrParameterZeroFiberTopologicalDiagram Stage sys)

def qCcrParameterZeroFiberTopologicalInjection (i : I) :
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys).obj i ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  colimit.ι (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i

/-- Canonical map from the relation-locus colimit to the ambient parameter
colimit, obtained by the natural inclusion of diagrams. -/
noncomputable def qCcrParameterZeroFiberToParameterColimit :
    qCcrParameterZeroFiberTopologicalColimit Stage sys ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  colim.map (qCcrParameterZeroFiberToParameterNatTrans Stage sys)

theorem qCcrParameterZeroFiberToParameterColimit_stage
    (i : I) :
    qCcrParameterZeroFiberTopologicalInjection Stage sys i ≫
        qCcrParameterZeroFiberToParameterColimit Stage sys =
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i ≫
        qCcrParameterTopologicalInjection Stage sys i := by
  exact colimit.ι_map
    (qCcrParameterZeroFiberToParameterNatTrans Stage sys) i

theorem qCcrParameterZeroFiberTopologicalInjection_transition
    {i j : I} (hij : i ≤ j)
    (p : {p : QCCRParameterSpace (Stage i) //
      p ∈ qCcrParameterZeroLocus (A := Stage i)}) :
    qCcrParameterZeroFiberTopologicalInjection Stage sys j
        (qCcrParameterZeroFiberTransitionMap Stage sys hij p) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i p := by
  have h :=
    (CategoryTheory.Limits.colimit.cocone
      (qCcrParameterZeroFiberTopologicalDiagram Stage sys)).w
      (CategoryTheory.homOfLE hij)
  simpa [qCcrParameterZeroFiberTopologicalInjection,
    qCcrParameterZeroFiberTopologicalDiagram] using congrArg (fun f => f p) h

/-- The ambient residual point associated with a fixed-q zero-locus point. -/
def qCcrSpecializationZeroLocusAmbientPoint
    {i : I} (q : Stage i)
    (p : {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) q}) :
    {p : QCCRParameterSpace (Stage i) //
      p ∈ qCcrParameterZeroLocus (A := Stage i)} :=
  ⟨qCcrSpecializationMap (A := Stage i) q p.1,
    (qCcrSpecializationZeroLocusMap (A := Stage i) q p).property.1⟩

theorem qCcrSpecialization_colimit_inclusion_stage
    {i : I} (q : Stage i)
    (p : {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) q}) :
    qCcrParameterZeroFiberToParameterColimit Stage sys
        (qCcrParameterZeroFiberTopologicalInjection Stage sys i
          (qCcrSpecializationZeroLocusAmbientPoint (Stage := Stage) q p)) =
      qCcrParameterTopologicalInjection Stage sys i
        (qCcrSpecializationZeroLocusAmbientPoint (Stage := Stage) q p).1 := by
  have h := qCcrParameterZeroFiberToParameterColimit_stage Stage sys i
  have hp := congrArg
    (fun f => f (qCcrSpecializationZeroLocusAmbientPoint (Stage := Stage) q p)) h
  simpa [qCcrParameterZeroFiberToParameterNatTrans] using hp

end InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
