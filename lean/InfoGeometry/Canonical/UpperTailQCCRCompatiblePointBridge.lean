import InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
import InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit

/-!
# Generic compatible q-CCR readout from an upper tail to the full colimit

This is the common universal-property layer for CAR, CCR, and Cuntz point
families.  It does not choose a representation: it transports any compatible
zero-fibre family along the upper-tail cocone into the full parameter colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.UpperTailQCCRCompatiblePointBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def upperTailCompatibleQCCRFullCocone
    (m : ℕ)
    (family : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m)) :
    Cocone ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) where
  pt := qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem
  ι :=
    { app := fun j =>
        TopCat.ofHom
          { toFun := fun _ =>
              qCcrParameterTopologicalInjection Stage
                T.toContinuousStarInductiveSystem j.1 (family.point j).1
            continuous_toFun := continuous_const }
      naturality := by
        intro j k f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro u
        change qCcrParameterTopologicalInjection Stage
            T.toContinuousStarInductiveSystem k.1 (family.point k).1 =
          qCcrParameterTopologicalInjection Stage
            T.toContinuousStarInductiveSystem j.1 (family.point j).1
        have hfamily := family.compatible (show j.1 ≤ k.1 from leOfHom f)
        have hfamily' := congrArg Subtype.val hfamily
        have hfamily'' :
            qCcrParameterTransitionMap Stage T.toContinuousStarInductiveSystem
                (show j.1 ≤ k.1 from leOfHom f) (family.point j).1 =
              (family.point k).1 := by
          simpa [qCcrParameterZeroFiberTransitionMap,
            upperTailContinuousStarSystem] using hfamily'
        have htransition := qCcrParameterTopologicalInjection_transition Stage
          T.toContinuousStarInductiveSystem (show j.1 ≤ k.1 from leOfHom f)
          (family.point j).1
        rw [← hfamily'']
        exact htransition }

noncomputable def upperTailCompatibleQCCRFullCoconeMap
    (m : ℕ)
    (family : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m)) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  topologicalDirectDescend
    ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit))
    (upperTailCompatibleQCCRFullCocone Stage T m family)

noncomputable def upperTailCompatibleQCCRFullParameterColimitMap
    (m : ℕ)
    (family : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m)) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  compatiblePointColimitMap
      (upperTailContinuousStarSystem Stage T m) family ≫
    qCcrParameterZeroFiberToParameterColimit
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
    upperTailQCCRParameterToFullColimitMap Stage T m

theorem upperTailCompatibleQCCRFullParameterColimitMap_stage_apply
    (m : ℕ)
    (family : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m))
    (j : UpperNatIndex m) (u : PUnit) :
    upperTailCompatibleQCCRFullParameterColimitMap Stage T m family
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (family.point j).1 := by
  have hpoint := compatiblePointColimitMap_stage_apply
    (upperTailContinuousStarSystem Stage T m) family j u
  have hincl := qCcrParameterZeroFiberToParameterColimit_stage
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
  have hincl' := congrArg (fun f => f (family.point j)) hincl
  have hincl'' :
      qCcrParameterZeroFiberToParameterColimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
          (qCcrParameterZeroFiberTopologicalInjection
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
            (family.point j)) =
        qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
          (family.point j).1 := by
    simpa [qCcrParameterZeroFiberToParameterNatTrans] using hincl'
  have htail := upperTailQCCRParameterToFullColimitMap_stage
    Stage T m j (family.point j).1
  calc
    upperTailCompatibleQCCRFullParameterColimitMap Stage T m family
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      upperTailQCCRParameterToFullColimitMap Stage T m
        (qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
          (family.point j).1) := by
        have h := congrArg
          (fun z => upperTailQCCRParameterToFullColimitMap Stage T m z)
          (congrArg
            (fun z => qCcrParameterZeroFiberToParameterColimit
              (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) z)
            hpoint)
        simpa [upperTailCompatibleQCCRFullParameterColimitMap] using
          h.trans (congrArg
            (fun z => upperTailQCCRParameterToFullColimitMap Stage T m z)
            hincl'')
    _ = qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (family.point j).1 := by
        exact htail

theorem upperTailCompatibleQCCRFullParameterColimitMap_eq_coconeMap
    (m : ℕ)
    (family : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m)) :
    upperTailCompatibleQCCRFullParameterColimitMap Stage T m family =
      upperTailCompatibleQCCRFullCoconeMap Stage T m family := by
  apply topologicalDirectDescend_unique
    ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit))
    (upperTailCompatibleQCCRFullCocone Stage T m family)
  intro j
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  exact upperTailCompatibleQCCRFullParameterColimitMap_stage_apply
    Stage T m family j u

theorem upperTailCompatibleQCCRFullCoconeMap_stage_apply
    (m : ℕ)
    (family : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m))
    (j : UpperNatIndex m) (u : PUnit) :
    upperTailCompatibleQCCRFullCoconeMap Stage T m family
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (family.point j).1 := by
  rw [← upperTailCompatibleQCCRFullParameterColimitMap_eq_coconeMap
    Stage T m family]
  exact upperTailCompatibleQCCRFullParameterColimitMap_stage_apply
    Stage T m family j u

theorem upperTailCompatibleQCCRFullParameterColimitMap_congr
    (m : ℕ)
    (family₁ family₂ : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m))
    (hfamily : ∀ j, family₁.point j = family₂.point j) :
    upperTailCompatibleQCCRFullParameterColimitMap Stage T m family₁ =
      upperTailCompatibleQCCRFullParameterColimitMap Stage T m family₂ := by
  apply colimit.hom_ext
  intro j
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  rw [upperTailCompatibleQCCRFullParameterColimitMap_stage_apply,
    upperTailCompatibleQCCRFullParameterColimitMap_stage_apply]
  exact congrArg Subtype.val (hfamily j)

theorem upperTailCompatibleQCCRFullCoconeMap_congr
    (m : ℕ)
    (family₁ family₂ : CompatibleQCCRPointFamily
      (upperTailContinuousStarSystem Stage T m))
    (hfamily : ∀ j, family₁.point j = family₂.point j) :
    upperTailCompatibleQCCRFullCoconeMap Stage T m family₁ =
      upperTailCompatibleQCCRFullCoconeMap Stage T m family₂ := by
  rw [← upperTailCompatibleQCCRFullParameterColimitMap_eq_coconeMap
      Stage T m family₁,
    ← upperTailCompatibleQCCRFullParameterColimitMap_eq_coconeMap
      Stage T m family₂,
    upperTailCompatibleQCCRFullParameterColimitMap_congr
      Stage T m family₁ family₂ hfamily]

end InfoGeometry.Canonical.UpperTailQCCRCompatiblePointBridge
