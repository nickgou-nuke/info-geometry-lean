import InfoGeometry.Canonical.UpperTailQCCRCompatiblePointBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CARCompatiblePointColimit
import InfoGeometry.Canonical.CCRCompatiblePointColimit

/-!
# CAR and CCR upper-tail readouts

The CAR and CCR witness families are transported through the common generic
upper-tail q-CCR colimit map.  This keeps the sign distinction in the point
family while sharing the same categorical ambient construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.UpperTailCARCCRPointBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.UpperTailQCCRCompatiblePointBridge
open InfoGeometry.Canonical.CARCompatiblePointColimit
open InfoGeometry.Canonical.CCRCompatiblePointColimit
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

noncomputable def upperTailCARFullParameterColimitMap
    (m : ℕ)
    (family : CompatibleCARPointFamily
      (upperTailContinuousStarSystem Stage T m)) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  upperTailCompatibleQCCRFullParameterColimitMap Stage T m family.toQCCR

theorem upperTailCARFullParameterColimitMap_stage_apply
    (m : ℕ)
    (family : CompatibleCARPointFamily
      (upperTailContinuousStarSystem Stage T m))
    (j : UpperNatIndex m) (u : PUnit) :
    upperTailCARFullParameterColimitMap Stage T m family
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (family.toQCCR.point j).1 := by
  exact upperTailCompatibleQCCRFullParameterColimitMap_stage_apply
    Stage T m family.toQCCR j u

noncomputable def upperTailCCRFullParameterColimitMap
    (m : ℕ)
    (family : CompatibleCCRPointFamily
      (upperTailContinuousStarSystem Stage T m)) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  upperTailCompatibleQCCRFullParameterColimitMap Stage T m family.toQCCR

theorem upperTailCCRFullParameterColimitMap_stage_apply
    (m : ℕ)
    (family : CompatibleCCRPointFamily
      (upperTailContinuousStarSystem Stage T m))
    (j : UpperNatIndex m) (u : PUnit) :
    upperTailCCRFullParameterColimitMap Stage T m family
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (family.toQCCR.point j).1 := by
  exact upperTailCompatibleQCCRFullParameterColimitMap_stage_apply
    Stage T m family.toQCCR j u

end InfoGeometry.Canonical.UpperTailCARCCRPointBridge
