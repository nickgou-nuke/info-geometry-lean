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

structure CompatibleQParameter where
  q : ∀ i, Stage i
  compatible : ∀ {i j : I} (hij : i ≤ j), sys.map hij (q i) = q j

def zeroQParameter : CompatibleQParameter Stage sys where
  q := fun _ => 0
  compatible := by intro i j hij; simp

def oneQParameter : CompatibleQParameter Stage sys where
  q := fun _ => 1
  compatible := by intro i j hij; simp

def negOneQParameter : CompatibleQParameter Stage sys where
  q := fun _ => -1
  compatible := by intro i j hij; simp

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
    (qdata : CompatibleQParameter Stage sys) : I ⥤ TopCat where
  obj i := TopCat.of
    {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)}
  map f := qCcrZeroLocusTransitionTopCatHom_compatible Stage sys
    (leOfHom f) (qdata.q _) (qdata.q _)
    (qdata.compatible (leOfHom f))
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
    (qdata : CompatibleQParameter Stage sys) : TopCat :=
  topologicalDirectColimit (qCcrZeroLocusTopologicalDiagram Stage sys qdata)

def qCcrZeroLocusTopologicalInjection
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata).obj i ⟶
      qCcrZeroLocusTopologicalColimit Stage sys qdata :=
  topologicalDirectInjection
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata) i

def qCcrZeroLocusSpecializationTopCatHom
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata).obj i ⟶
      (qCcrParameterZeroFiberTopologicalDiagram Stage sys).obj i :=
  qCcrSpecializationZeroLocusTopCatHom (A := Stage i) (qdata.q i) ≫
    qCcrParameterZeroLocusFiberInclusionTopCatHom (Stage := Stage) i
      (qdata.q i)

theorem qCcrZeroLocusSpecializationTopCatHom_injective
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    Function.Injective (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i) := by
  intro p₁ p₂ h
  apply qCcrSpecializationZeroLocusMap_injective (A := Stage i) (qdata.q i)
  apply Subtype.ext
  simpa [qCcrZeroLocusSpecializationTopCatHom,
    qCcrParameterZeroLocusFiberInclusionTopCatHom,
    qCcrSpecializationZeroLocusTopCatHom] using congrArg Subtype.val h

theorem qCcrZeroLocusSpecializationTopCatHom_isEmbedding
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    Topology.IsEmbedding (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i) := by
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
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    Topology.IsClosedEmbedding
      (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i) := by
  let hs : Set (QCCRParameterSpace (Stage i)) :=
    qCcrParameterZeroLocusFiber (A := Stage i) (qdata.q i)
  let ht : Set (QCCRParameterSpace (Stage i)) :=
    qCcrParameterZeroLocus (A := Stage i)
  have hst : hs ⊆ ht := by
    intro p hp
    exact hp.1
  have hclosed : IsClosed hs := by
    simpa [hs] using
      (qCcrParameterZeroLocusFiber_closed (A := Stage i) (qdata.q i))
  have hinclusion :
      Topology.IsClosedEmbedding (Set.inclusion hst) :=
    Topology.IsClosedEmbedding.inclusion hst
      (hclosed.preimage continuous_subtype_val)
  let e :
      {p : (Stage i) × (Stage i) //
        p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)} ≃ₜ
        qCcrParameterZeroLocusFiberType (A := Stage i) (qdata.q i) :=
    { toFun := qCcrSpecializationZeroLocusMap (A := Stage i) (qdata.q i)
      invFun := qCcrSpecializationZeroLocusFiberMap (A := Stage i) (qdata.q i)
      left_inv := qCcrSpecializationZeroLocusMap_leftInverse
        (A := Stage i) (qdata.q i)
      right_inv := qCcrSpecializationZeroLocusMap_rightInverse
        (A := Stage i) (qdata.q i)
      continuous_toFun := continuous_qCcrSpecializationZeroLocusMap
        (A := Stage i) (qdata.q i)
      continuous_invFun := continuous_qCcrSpecializationZeroLocusFiberMap
        (A := Stage i) (qdata.q i) }
  have hspecial : Topology.IsClosedEmbedding e := e.isClosedEmbedding
  change Topology.IsClosedEmbedding
    ((Set.inclusion hst) ∘
      qCcrSpecializationZeroLocusMap (A := Stage i) (qdata.q i))
  exact hinclusion.comp hspecial

theorem qCcrZeroLocusSpecialization_natural
    (qdata : CompatibleQParameter Stage sys)
    {i j : I} (hij : i ≤ j) :
    qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      qCcrZeroLocusTransitionTopCatHom_compatible Stage sys hij
        (qdata.q i) (qdata.q j) (qdata.compatible hij) ≫
        qCcrZeroLocusSpecializationTopCatHom Stage sys qdata j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  change qCcrParameterTransitionMap Stage sys hij
      (qCcrSpecializationMap (A := Stage i) (qdata.q i) p.1) =
    qCcrSpecializationMap (A := Stage j) (qdata.q j)
      (qCcrOperatorPairTransitionMap Stage sys hij p.1)
  simp [qCcrParameterTransitionMap, qCcrSpecializationMap,
    qCcrOperatorPairTransitionMap, qdata.compatible hij]

def qCcrZeroLocusSpecializationNatTrans
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusTopologicalDiagram Stage sys qdata ⟶
      qCcrParameterZeroFiberTopologicalDiagram Stage sys where
  app i := qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i
  naturality := by
    intro i j f
    simpa [qCcrZeroLocusTopologicalDiagram] using
      (qCcrZeroLocusSpecialization_natural Stage sys qdata (leOfHom f)).symm

noncomputable def qCcrZeroLocusSpecializationColimitMap
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusTopologicalColimit Stage sys qdata ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  colim.map (qCcrZeroLocusSpecializationNatTrans Stage sys qdata)

theorem qCcrZeroLocusSpecializationColimitMap_stage
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    qCcrZeroLocusTopologicalInjection Stage sys qdata i ≫
        qCcrZeroLocusSpecializationColimitMap Stage sys qdata =
      qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i ≫
        qCcrParameterZeroFiberTopologicalInjection Stage sys i := by
  change topologicalDirectInjection
      (qCcrZeroLocusTopologicalDiagram Stage sys qdata) i ≫
      colim.map (qCcrZeroLocusSpecializationNatTrans Stage sys qdata) =
    (qCcrZeroLocusSpecializationNatTrans Stage sys qdata).app i ≫
      topologicalDirectInjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
  exact colimit.ι_map (qCcrZeroLocusSpecializationNatTrans Stage sys qdata) i

def qCcrZeroLocusSpecializationCocone
    (qdata : CompatibleQParameter Stage sys) :
    Cocone (qCcrZeroLocusTopologicalDiagram Stage sys qdata) where
  pt := qCcrParameterZeroFiberTopologicalColimit Stage sys
  ι :=
    { app := fun i =>
        qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i ≫
          qCcrParameterZeroFiberTopologicalInjection Stage sys i
      naturality := by
        intro i j f
        have hspec := qCcrZeroLocusSpecialization_natural
          Stage sys qdata (leOfHom f)
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
          (qCcrZeroLocusTopologicalDiagram Stage sys qdata).map f ≫
                (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata j ≫
                  qCcrParameterZeroFiberTopologicalInjection Stage sys j) =
                (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i ≫
                qCcrParameterZeroFiberTransitionTopCatHom Stage sys (leOfHom f)) ≫
                  qCcrParameterZeroFiberTopologicalInjection Stage sys j := by
                    change qCcrZeroLocusTransitionTopCatHom_compatible Stage sys
                        (leOfHom f) (qdata.q i) (qdata.q j)
                        (qdata.compatible (leOfHom f)) ≫
                        (qCcrZeroLocusSpecializationTopCatHom Stage sys qdata j ≫
                          qCcrParameterZeroFiberTopologicalInjection Stage sys j) = _
                    rw [← Category.assoc, ← hspec]
          _ = qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i ≫
                qCcrParameterZeroFiberTopologicalInjection Stage sys i := by
                    rw [Category.assoc, hinc] }

noncomputable def qCcrZeroLocusSpecializationCoconeMap
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusTopologicalColimit Stage sys qdata ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  topologicalDirectDescend
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata)
    (qCcrZeroLocusSpecializationCocone Stage sys qdata)

theorem qCcrZeroLocusSpecializationColimitMap_eq_coconeMap
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusSpecializationColimitMap Stage sys qdata =
      qCcrZeroLocusSpecializationCoconeMap Stage sys qdata := by
  apply topologicalDirectDescend_unique
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata)
    (qCcrZeroLocusSpecializationCocone Stage sys qdata)
  intro i
  exact qCcrZeroLocusSpecializationColimitMap_stage Stage sys qdata i

theorem qCcrZeroLocusSpecializationCoconeMap_stage
    (qdata : CompatibleQParameter Stage sys) (i : I)
    (p : {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)}) :
    qCcrZeroLocusSpecializationCoconeMap Stage sys qdata
        (qCcrZeroLocusTopologicalInjection Stage sys qdata i p) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        ((qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i) p) := by
  rw [← qCcrZeroLocusSpecializationColimitMap_eq_coconeMap Stage sys qdata]
  exact congrArg (fun f => f p)
    (qCcrZeroLocusSpecializationColimitMap_stage Stage sys qdata i)

noncomputable def qCcrZeroLocusParameterColimitMap
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusTopologicalColimit Stage sys qdata ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusSpecializationColimitMap Stage sys qdata ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem qCcrZeroLocusParameterColimitMap_stage_apply
    (qdata : CompatibleQParameter Stage sys) (i : I)
    (p : {p : Stage i × Stage i //
      p ∈ qCcrZeroLocus (A := Stage i) (qdata.q i)}) :
    qCcrZeroLocusParameterColimitMap Stage sys qdata
        (qCcrZeroLocusTopologicalInjection Stage sys qdata i p) =
      qCcrParameterTopologicalInjection Stage sys i
        (qCcrSpecializationZeroLocusAmbientPoint
          (Stage := Stage) (qdata.q i) p).1 := by
  have hspecial := qCcrZeroLocusSpecializationColimitMap_stage
    Stage sys qdata i
  have hspecial' := congrArg (fun f => f p) hspecial
  have hambient := qCcrSpecialization_colimit_inclusion_stage
    Stage sys (qdata.q i) p
  calc
    qCcrZeroLocusParameterColimitMap Stage sys qdata
        (qCcrZeroLocusTopologicalInjection Stage sys qdata i p) =
      qCcrParameterZeroFiberToParameterColimit Stage sys
        (qCcrParameterZeroFiberTopologicalInjection Stage sys i
          ((qCcrZeroLocusSpecializationTopCatHom Stage sys qdata i) p)) := by
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
      (zeroQParameter Stage sys) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusParameterColimitMap Stage sys (zeroQParameter Stage sys)

noncomputable def oneQParameterColimitMap :
    qCcrZeroLocusTopologicalColimit Stage sys
      (oneQParameter Stage sys) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusParameterColimitMap Stage sys (oneQParameter Stage sys)

noncomputable def negOneQParameterColimitMap :
    qCcrZeroLocusTopologicalColimit Stage sys
      (negOneQParameter Stage sys) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrZeroLocusParameterColimitMap Stage sys (negOneQParameter Stage sys)

end InfoGeometry.Canonical.FilteredQCCRFixedParameterColimit
