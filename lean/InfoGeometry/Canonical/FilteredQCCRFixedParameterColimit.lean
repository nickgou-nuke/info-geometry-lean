import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
import InfoGeometry.Canonical.CARCCRParameterFiberSeparation

/-!
# Filtered colimits of compatible fixed-q q-CCR loci

When the q-parameter itself varies by stage but is preserved by the star
transitions, the stagewise q-zero loci form their own `TopCat` diagram.  This
owner forms that colimit and descends the canonical specialization maps into
the ambient residual-zero-fibre colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredQCCRFixedParameterColimit

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.CARCCRParameterFiberSeparation
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

structure CompatibleQParameter
    (sys : ContinuousStarInductiveSystem Stage) where
  q : ∀ i, Stage i

def zeroQParameter : CompatibleQParameter Stage sys where
  q := fun _ => 0

theorem zeroQParameter_compatible :
    ∀ {i j : I} (hij : i ≤ j), sys.map hij ((zeroQParameter Stage sys).q i) =
      (zeroQParameter Stage sys).q j := by
  intro i j hij
  change sys.map hij 0 = 0
  exact map_zero (sys.map hij)

def oneQParameter : CompatibleQParameter Stage sys where
  q := fun _ => 1

theorem oneQParameter_compatible :
    ∀ {i j : I} (hij : i ≤ j), sys.map hij ((oneQParameter Stage sys).q i) =
      (oneQParameter Stage sys).q j := by
  intro i j hij
  change sys.map hij 1 = 1
  exact map_one (sys.map hij)

def negOneQParameter : CompatibleQParameter Stage sys where
  q := fun _ => -1

theorem negOneQParameter_compatible :
    ∀ {i j : I} (hij : i ≤ j), sys.map hij ((negOneQParameter Stage sys).q i) =
      (negOneQParameter Stage sys).q j := by
  intro i j hij
  change sys.map hij (-1) = -1
  rw [map_neg, map_one]

def qCcrZeroLocusTransitionTopCatHom_compatible
    {i j : I} (hij : i ≤ j) (qᵢ : Stage i) (qⱼ : Stage j)
    (hq : sys.map hij qᵢ = qⱼ) :
    TopCat.of {p : Stage i × Stage i //
        p ∈ qCcrZeroLocus (A := Stage i) qᵢ} ⟶
      TopCat.of {p : Stage j × Stage j //
        p ∈ qCcrZeroLocus (A := Stage j) qⱼ} :=
  TopCat.ofHom
    { toFun := fun p =>
        ⟨(qCcrZeroLocusTransitionMap Stage sys hij qᵢ p).1, by
          rw [← hq]
          exact (qCcrZeroLocusTransitionMap Stage sys hij qᵢ p).2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hcont : Continuous (fun p :
            {p : Stage i × Stage i //
              p ∈ qCcrZeroLocus (A := Stage i) qᵢ} =>
            (qCcrZeroLocusTransitionMap Stage sys hij qᵢ p).1) := by
          exact (continuous_subtype_val.comp
            (continuous_qCcrZeroLocusTransitionMap Stage sys hij qᵢ))
        exact hcont }

def qCcrZeroLocusTopologicalDiagram
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j),
      sys.map hij (qdata.q i) = qdata.q j) : I ⥤ TopCat where
  obj i := TopCat.of
    {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)}
  map f := qCcrZeroLocusTransitionTopCatHom_compatible Stage sys
    (leOfHom f) (qdata.q _) (qdata.q _)
    (hq (leOfHom f))
  map_id i := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    simp [qCcrZeroLocusTransitionTopCatHom_compatible,
      qCcrZeroLocusTransitionMap, qCcrOperatorPairTransitionMap,
      sys.map_id]
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    dsimp [qCcrZeroLocusTransitionTopCatHom_compatible,
      qCcrZeroLocusTransitionMap, qCcrOperatorPairTransitionMap]
    have hfg := (sys.map_comp (leOfHom f) (leOfHom g)).symm
    apply Prod.ext
    · exact congrArg (fun e => e p.1.1) hfg
    · exact congrArg (fun e => e p.1.2) hfg

abbrev qCcrZeroLocusTopologicalColimit
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j),
      sys.map hij (qdata.q i) = qdata.q j) : TopCat :=
  colimit (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq)

def qCcrZeroLocusTopologicalInjection
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j),
      sys.map hij (qdata.q i) = qdata.q j) (i : I) :
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq).obj i ⟶
      qCcrZeroLocusTopologicalColimit Stage sys qdata hq :=
  colimit.ι
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq) i

def qCcrZeroLocusSpecializationTopCatHom
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j),
      sys.map hij (qdata.q i) = qdata.q j) (i : I) :
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq).obj i ⟶
      (qCcrParameterZeroFiberTopologicalDiagram Stage sys).obj i :=
  qCcrSpecializationZeroLocusTopCatHom (A := Stage i) (qdata.q i) ≫
    qCcrParameterZeroLocusFiberInclusionTopCatHom (Stage := Stage) i
      (qdata.q i)

theorem qCcrZeroLocusSpecializationTopCatHom_injective
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I) :
    Function.Injective (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i) := by
  intro p₁ p₂ h
  apply qCcrSpecializationZeroLocusMap_injective (A := Stage i) (qdata.q i)
  apply Subtype.ext
  simpa [qCcrZeroLocusSpecializationTopCatHom,
    qCcrParameterZeroLocusFiberInclusionTopCatHom,
    qCcrSpecializationZeroLocusTopCatHom] using congrArg Subtype.val h

theorem qCcrZeroLocusSpecializationTopCatHom_isEmbedding
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I) :
    Topology.IsEmbedding (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i) := by
  have hspecial :
      Topology.IsEmbedding
        (qCcrSpecializationZeroLocusMap (A := Stage i) (qdata.q i)) :=
    (qCcrSpecializationZeroLocusMap_leftInverse (A := Stage i) (qdata.q i)).isEmbedding
      (continuous_qCcrSpecializationZeroLocusFiberMap (A := Stage i) (qdata.q i))
      (continuous_qCcrSpecializationZeroLocusMap (A := Stage i) (qdata.q i))
  have hinclusion :
      Topology.IsEmbedding
        (fun p : qCcrParameterZeroLocusFiberType (A := Stage i) (qdata.q i) =>
          (⟨p.1, p.2.1⟩ :
            {p : QCCRParameterSpace (Stage i) //
              p ∈ qCcrParameterZeroLocus (A := Stage i)})) := by
    exact Topology.IsEmbedding.inclusion (fun _ hp => hp.1)
  exact hinclusion.comp hspecial

theorem qCcrZeroLocusSpecializationTopCatHom_isClosedEmbedding
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I) :
    Topology.IsClosedEmbedding
      (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i) := by
  have hst : qCcrParameterZeroLocusFiber (A := Stage i) (qdata.q i) ⊆
      qCcrParameterZeroLocus (A := Stage i) := fun _ hp => hp.1
  have hinclusion :
      Topology.IsClosedEmbedding (Set.inclusion hst) :=
    qCcrParameterZeroLocusFiber_inclusion_isClosedEmbedding
      (A := Stage i) (qdata.q i)
  have hspecial : Topology.IsClosedEmbedding
      (qCcrSpecializationZeroLocusMap (A := Stage i) (qdata.q i)) :=
    qCcrSpecializationZeroLocusMap_isClosedEmbedding (A := Stage i) (qdata.q i)
  change Topology.IsClosedEmbedding
    ((Set.inclusion hst) ∘
      qCcrSpecializationZeroLocusMap (A := Stage i) (qdata.q i))
  exact hinclusion.comp hspecial

theorem qCcrZeroLocusSpecialization_natural
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    {i j : I} (hij : i ≤ j) :
    qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      qCcrZeroLocusTransitionTopCatHom_compatible Stage sys hij
        (qdata.q i) (qdata.q j) (hq hij) ≫
        qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  change qCcrParameterTransitionMap Stage sys hij
      (qCcrSpecializationMap (A := Stage i) (qdata.q i) p.1) =
    qCcrSpecializationMap (A := Stage j) (qdata.q j)
      (qCcrOperatorPairTransitionMap Stage sys hij p.1)
  simp [qCcrParameterTransitionMap, qCcrSpecializationMap,
    qCcrOperatorPairTransitionMap, hq hij]

def qCcrZeroLocusSpecializationNatTrans
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j),
      sys.map hij (qdata.q i) = qdata.q j) :
    qCcrZeroLocusTopologicalDiagram Stage sys qdata hq ⟶
      qCcrParameterZeroFiberTopologicalDiagram Stage sys where
  app i := qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i
  naturality := by
    intro i j f
    simpa [qCcrZeroLocusTopologicalDiagram] using
      (qCcrZeroLocusSpecialization_natural Stage sys qdata hq (leOfHom f)).symm

theorem qCcrZeroLocusSpecializationNatTrans_app_isClosedEmbedding
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I) :
    Topology.IsClosedEmbedding
      ((qCcrZeroLocusSpecializationNatTrans Stage sys qdata hq).app i) := by
  simpa [qCcrZeroLocusSpecializationNatTrans] using
    qCcrZeroLocusSpecializationTopCatHom_isClosedEmbedding Stage sys qdata hq i

theorem qCcrZeroLocusSpecializationNatTrans_app_closed_range
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I) :
    IsClosed (Set.range
      ((qCcrZeroLocusSpecializationNatTrans Stage sys qdata hq).app i)) := by
  exact (qCcrZeroLocusSpecializationNatTrans_app_isClosedEmbedding
    Stage sys qdata hq i).isClosed_range

noncomputable def qCcrZeroLocusSpecializationColimitMap
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j) :
    qCcrZeroLocusTopologicalColimit Stage sys qdata hq ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  colim.map (qCcrZeroLocusSpecializationNatTrans Stage sys qdata hq)

theorem qCcrZeroLocusSpecializationColimitMap_stage
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I) :
    qCcrZeroLocusTopologicalInjection Stage sys qdata hq i ≫
        qCcrZeroLocusSpecializationColimitMap Stage sys qdata hq =
      qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i ≫
        qCcrParameterZeroFiberTopologicalInjection Stage sys i := by
  change colimit.ι
      (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq) i ≫
      colim.map (qCcrZeroLocusSpecializationNatTrans Stage sys qdata hq) =
    (qCcrZeroLocusSpecializationNatTrans Stage sys qdata hq).app i ≫
      colimit.ι
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
  exact colimit.ι_map (qCcrZeroLocusSpecializationNatTrans Stage sys qdata hq) i

def qCcrZeroLocusSpecializationCocone
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j) :
    Cocone (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq) where
  pt := qCcrParameterZeroFiberTopologicalColimit Stage sys
  ι :=
    { app := fun i =>
        qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i ≫
          qCcrParameterZeroFiberTopologicalInjection Stage sys i
      naturality := by
        intro i j f
        have hspec := qCcrZeroLocusSpecialization_natural
          Stage sys qdata hq (leOfHom f)
        have hinc :
            qCcrParameterZeroFiberTransitionTopCatHom Stage sys (leOfHom f) ≫
                qCcrParameterZeroFiberTopologicalInjection Stage sys j =
              qCcrParameterZeroFiberTopologicalInjection Stage sys i := by
          apply TopCat.hom_ext
          apply ContinuousMap.ext
          intro p
          exact qCcrParameterZeroFiberTopologicalInjection_transition
            Stage sys (leOfHom f) p
        calc
          (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq).map f ≫
                (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq j ≫
                  qCcrParameterZeroFiberTopologicalInjection Stage sys j) =
                (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i ≫
                qCcrParameterZeroFiberTransitionTopCatHom Stage sys (leOfHom f)) ≫
                  qCcrParameterZeroFiberTopologicalInjection Stage sys j := by
                    change qCcrZeroLocusTransitionTopCatHom_compatible Stage sys
                        (leOfHom f) (qdata.q i) (qdata.q j)
                        (hq (leOfHom f)) ≫
                        (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq j ≫
                          qCcrParameterZeroFiberTopologicalInjection Stage sys j) = _
                    rw [← Category.assoc, ← hspec]
          _ = qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i ≫
                qCcrParameterZeroFiberTopologicalInjection Stage sys i := by
                    rw [Category.assoc, hinc] }

noncomputable def qCcrZeroLocusSpecializationCoconeMap
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j) :
    qCcrZeroLocusTopologicalColimit Stage sys qdata hq ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  colimit.desc
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq)
    (qCcrZeroLocusSpecializationCocone Stage sys qdata hq)

theorem qCcrZeroLocusSpecializationColimitMap_eq_coconeMap
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j) :
    qCcrZeroLocusSpecializationColimitMap Stage sys qdata hq =
      qCcrZeroLocusSpecializationCoconeMap Stage sys qdata hq := by
  apply topologicalDirectDescend_unique
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata hq)
    (qCcrZeroLocusSpecializationCocone Stage sys qdata hq)
  intro i
  exact qCcrZeroLocusSpecializationColimitMap_stage Stage sys qdata hq i

theorem qCcrZeroLocusSpecializationCoconeMap_stage
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I)
    (p : {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)}) :
    qCcrZeroLocusSpecializationCoconeMap Stage sys qdata hq
        (qCcrZeroLocusTopologicalInjection Stage sys qdata hq i p) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        ((qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i) p) := by
  rw [← qCcrZeroLocusSpecializationColimitMap_eq_coconeMap Stage sys qdata hq]
  exact congrArg (fun f => f p)
    (qCcrZeroLocusSpecializationColimitMap_stage Stage sys qdata hq i)

noncomputable def qCcrZeroLocusParameterColimitMap
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j) :
    qCcrZeroLocusTopologicalColimit Stage sys qdata hq ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusSpecializationColimitMap Stage sys qdata hq ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem qCcrZeroLocusParameterColimitMap_stage_apply
    (qdata : CompatibleQParameter Stage sys)
    (hq : ∀ {i j : I} (hij : i ≤ j), sys.map hij (qdata.q i) = qdata.q j)
    (i : I)
    (p : {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)}) :
    qCcrZeroLocusParameterColimitMap Stage sys qdata hq
        (qCcrZeroLocusTopologicalInjection Stage sys qdata hq i p) =
      qCcrParameterTopologicalInjection Stage sys i
        (qCcrSpecializationZeroLocusAmbientPoint
          (Stage := Stage) (qdata.q i) p).1 := by
  have hspecial := qCcrZeroLocusSpecializationColimitMap_stage
    Stage sys qdata hq i
  have hspecial' := congrArg (fun f => f p) hspecial
  have hambient := qCcrSpecialization_colimit_inclusion_stage
    Stage sys (qdata.q i) p
  calc
    qCcrZeroLocusParameterColimitMap Stage sys qdata hq
        (qCcrZeroLocusTopologicalInjection Stage sys qdata hq i p) =
      qCcrParameterZeroFiberToParameterColimit Stage sys
        (qCcrParameterZeroFiberTopologicalInjection Stage sys i
          ((qCcrZeroLocusSpecializationTopCatHom Stage sys qdata hq i) p)) := by
        have h := congrArg
          (fun z => qCcrParameterZeroFiberToParameterColimit Stage sys z)
          hspecial'
        simpa [qCcrZeroLocusParameterColimitMap] using h
    _ = qCcrParameterTopologicalInjection Stage sys i
        (qCcrSpecializationZeroLocusAmbientPoint
          (Stage := Stage) (qdata.q i) p).1 := by
        simpa [qCcrZeroLocusSpecializationTopCatHom,
          qCcrSpecializationZeroLocusAmbientPoint] using hambient

noncomputable def zeroQParameterColimitMap :
    qCcrZeroLocusTopologicalColimit Stage sys
      (zeroQParameter Stage sys) (zeroQParameter_compatible Stage sys) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusParameterColimitMap Stage sys (zeroQParameter Stage sys)
    (zeroQParameter_compatible Stage sys)

noncomputable def oneQParameterColimitMap :
    qCcrZeroLocusTopologicalColimit Stage sys
      (oneQParameter Stage sys) (oneQParameter_compatible Stage sys) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusParameterColimitMap Stage sys (oneQParameter Stage sys)
    (oneQParameter_compatible Stage sys)

noncomputable def negOneQParameterColimitMap :
    qCcrZeroLocusTopologicalColimit Stage sys
      (negOneQParameter Stage sys) (negOneQParameter_compatible Stage sys) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusParameterColimitMap Stage sys (negOneQParameter Stage sys)
    (negOneQParameter_compatible Stage sys)

end InfoGeometry.Canonical.FilteredQCCRFixedParameterColimit
