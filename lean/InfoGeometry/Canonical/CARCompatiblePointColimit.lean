import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit

/-!
# Compatible CAR witnesses in the filtered q-CCR zero-fiber colimit

This owner converts a stagewise CAR pair, together with its transition laws,
into the generic compatible zero-fiber family.  The resulting colimit map is
therefore a categorical descent of CAR witnesses, not a disconnected endpoint
construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.CARCompatiblePointColimit

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {I : Type u} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

structure CompatibleCARPointFamily where
  c : ∀ i, Stage i
  cstar : ∀ i, Stage i
  relation : ∀ i, c i * cstar i + cstar i * c i = 1
  compatible_c : ∀ {i j : I} (hij : i ≤ j), sys.map hij (c i) = c j
  compatible_cstar : ∀ {i j : I} (hij : i ≤ j),
    sys.map hij (cstar i) = cstar j

def CompatibleCARPointFamily.toQCCR
    (family : CompatibleCARPointFamily sys) :
    CompatibleQCCRPointFamily sys where
  point i :=
    ⟨carParameterPoint (family.c i) (family.cstar i), by
      dsimp [qCcrParameterZeroLocus, qCcrParameterResidualContinuousMap, carParameterPoint]
      exact car_is_neg_one_qccr (family.c i) (family.cstar i) (family.relation i)⟩
  compatible := by
    intro i j hij
    apply Subtype.ext
    change (sys.map hij (family.c i),
        (sys.map hij (family.cstar i), sys.map hij (-1 : Stage i))) =
      (family.c j, (family.cstar j, (-1 : Stage j)))
    simp [family.compatible_c hij, family.compatible_cstar hij]

noncomputable def carCompatiblePointColimitMap
    (family : CompatibleCARPointFamily sys) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  compatiblePointColimitMap sys family.toQCCR

theorem carCompatiblePointColimitMap_stage_apply
    (family : CompatibleCARPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    carCompatiblePointColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        (family.toQCCR.point i) := by
  exact compatiblePointColimitMap_stage_apply sys family.toQCCR i u

noncomputable def carCompatiblePointParameterColimitMap
    (family : CompatibleCARPointFamily sys) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  carCompatiblePointColimitMap sys family ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem carCompatiblePointParameterColimitMap_stage_apply
    (family : CompatibleCARPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    carCompatiblePointParameterColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterTopologicalInjection Stage sys i
        (family.toQCCR.point i).1 := by
  have hincl := qCcrParameterZeroFiberToParameterColimit_stage Stage sys i
  have hincl' := congrArg (fun f => f (family.toQCCR.point i)) hincl
  change qCcrParameterZeroFiberToParameterColimit Stage sys
      (qCcrParameterZeroFiberTopologicalInjection Stage sys i
        (family.toQCCR.point i)) =
    qCcrParameterTopologicalInjection Stage sys i (family.toQCCR.point i).1 at hincl'
  change qCcrParameterZeroFiberToParameterColimit Stage sys
      (carCompatiblePointColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u)) =
    qCcrParameterTopologicalInjection Stage sys i (family.toQCCR.point i).1
  rw [carCompatiblePointColimitMap_stage_apply]
  exact hincl'

end InfoGeometry.Canonical.CARCompatiblePointColimit
