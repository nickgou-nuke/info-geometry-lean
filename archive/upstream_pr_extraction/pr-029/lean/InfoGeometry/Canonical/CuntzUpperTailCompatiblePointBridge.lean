import InfoGeometry.Canonical.CuntzCompatiblePointColimit
import InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout

/-!
# Upper-tail specialization of the compatible Cuntz point descent

The upper-tail Cuntz generator readout is an instance of the generic
compatible-family construction.  This owner records that factorization
without replacing the existing upper-tail colimit owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailCompatiblePointBridge

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.CuntzCompatiblePointColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open CStarStateColimit.Native
open FilteredColimit.Native.Topological
open InfoGeometry.Physics.CStarCuntzTensorQuotient

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def upperTailCompatibleCuntzPointFamily
    (m : ℕ) (i : Fin m) :
    CompatibleCuntzPointFamily
      (upperTailContinuousStarSystem Stage T m) where
  c j := star ((T.family j.1).S (Fin.castLE j.2 i))
  cstar j := (T.family j.1).S (Fin.castLE j.2 i)
  relation j := by
    exact (T.family j.1).isometry_relation (Fin.castLE j.2 i)
  compatible_c := by
    intro j k hjk
    simp [upperTailContinuousStarSystem, T.map_generator, map_star]
  compatible_cstar := by
    intro j k hjk
    simp [upperTailContinuousStarSystem, T.map_generator]

theorem upperTailCompatibleCuntzPointFamily_toQCCR_point
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    (upperTailCompatibleCuntzPointFamily Stage T m i).toQCCR.point j =
      upperTailCuntzQCCRPoint Stage T m i j := by
  apply Subtype.ext
  rfl

noncomputable def upperTailCompatibleCuntzParameterColimitMap
    (m : ℕ) (i : Fin m) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  cuntzCompatiblePointParameterColimitMap
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCompatibleCuntzPointFamily Stage T m i)

theorem upperTailCompatibleCuntzParameterColimitMap_stage_apply
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (u : PUnit) :
    upperTailCompatibleCuntzParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
  have h := cuntzCompatiblePointParameterColimitMap_stage_apply
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCompatibleCuntzPointFamily Stage T m i) j u
  simpa [upperTailCompatibleCuntzParameterColimitMap,
    upperTailCompatibleCuntzPointFamily_toQCCR_point] using h

noncomputable def upperTailCompatibleCuntzFullParameterColimitMap
    (m : ℕ) (i : Fin m) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  upperTailCompatibleCuntzParameterColimitMap Stage T m i ≫
    upperTailQCCRParameterToFullColimitMap Stage T m

theorem upperTailCompatibleCuntzFullParameterColimitMap_stage_apply
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (u : PUnit) :
    upperTailCompatibleCuntzFullParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
  have htail := upperTailCompatibleCuntzParameterColimitMap_stage_apply
    Stage T m i j u
  have hfull := upperTailQCCRParameterToFullColimitMap_stage
    Stage T m j (upperTailCuntzQCCRPoint Stage T m i j).1
  calc
    upperTailCompatibleCuntzFullParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      upperTailQCCRParameterToFullColimitMap Stage T m
        (qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
          (upperTailCuntzQCCRPoint Stage T m i j).1) := by
        have h := congrArg
          (fun z => upperTailQCCRParameterToFullColimitMap Stage T m z) htail
        simpa [upperTailCompatibleCuntzFullParameterColimitMap] using h
    _ = qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
        exact hfull

theorem upperTailCompatibleCuntzFullParameterColimitMap_cutoff_compat
    (m n : ℕ) (hmn : m ≤ n) (i : Fin m)
    (j : UpperNatIndex n) (u : PUnit) :
    upperTailCompatibleCuntzFullParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit))
          ⟨j.1, le_trans hmn j.2⟩ u) =
      upperTailCompatibleCuntzFullParameterColimitMap Stage T n (Fin.castLE hmn i)
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex n)).obj (TopCat.of PUnit)) j u) := by
  have hm := upperTailCompatibleCuntzFullParameterColimitMap_stage_apply
    Stage T m i ⟨j.1, le_trans hmn j.2⟩ u
  have hn := upperTailCompatibleCuntzFullParameterColimitMap_stage_apply
    Stage T n (Fin.castLE hmn i) j u
  have hpoint :
      (upperTailCuntzQCCRPoint Stage T m i
        ⟨j.1, le_trans hmn j.2⟩).1 =
      (upperTailCuntzQCCRPoint Stage T n (Fin.castLE hmn i) j).1 := by
    apply Prod.ext
    · congr 1
    · apply Prod.ext
      · congr 1
      · rfl
  rw [hm, hn, hpoint]

end InfoGeometry.Canonical.CuntzUpperTailCompatiblePointBridge
