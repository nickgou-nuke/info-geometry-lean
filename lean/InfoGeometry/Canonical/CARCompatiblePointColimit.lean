import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
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
  map_c : ∀ {i j : I} (hij : i ≤ j), sys.map hij (c i) = c j
  map_cstar : ∀ {i j : I} (hij : i ≤ j),
    sys.map hij (cstar i) = cstar j

def CompatibleCARPointFamily.toQCCR
    (family : CompatibleCARPointFamily sys) :
    CompatibleQCCRPointFamily sys where
  point i :=
    ⟨carParameterPoint (family.c i) (family.cstar i), by
      change qCcrParameterResidualContinuousMap (A := Stage i)
          (carParameterPoint (family.c i) (family.cstar i)) = 0
      simpa [qCcrParameterResidualContinuousMap, carParameterPoint] using
        car_is_neg_one_qccr (family.c i) (family.cstar i) (family.relation i)⟩
theorem CompatibleCARPointFamily.toQCCR_compatible
    (family : CompatibleCARPointFamily sys) :
    ∀ {i j : I} (hij : i ≤ j),
      qCcrParameterZeroFiberTransitionMap Stage sys hij
          (family.toQCCR.point i) = family.toQCCR.point j := by
    intro i j hij
    apply Subtype.ext
    change qCcrParameterTransitionMap Stage sys hij
        (carParameterPoint (family.c i) (family.cstar i)) =
      carParameterPoint (family.c j) (family.cstar j)
    simp [qCcrParameterTransitionMap, carParameterPoint,
      family.map_c hij, family.map_cstar hij]

noncomputable def carCompatiblePointColimitMap
    (family : CompatibleCARPointFamily sys) :
    colimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  compatiblePointColimitMap sys family.toQCCR
    family.toQCCR_compatible

theorem carCompatiblePointColimitMap_stage_apply
    (family : CompatibleCARPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    carCompatiblePointColimitMap sys family
        (colimit.ι ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        (family.toQCCR.point i) := by
  exact compatiblePointColimitMap_stage_apply sys family.toQCCR
    family.toQCCR_compatible i u

noncomputable def carCompatiblePointParameterColimitMap
    (family : CompatibleCARPointFamily sys) :
    colimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  carCompatiblePointColimitMap sys family ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem carCompatiblePointParameterColimitMap_stage_apply
    (family : CompatibleCARPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    carCompatiblePointParameterColimitMap sys family
        (colimit.ι ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterTopologicalInjection Stage sys i
        (family.toQCCR.point i).1 := by
  have hpoint := compatiblePointColimitMap_stage_apply sys family.toQCCR
    family.toQCCR_compatible i u
  have hincl := qCcrParameterZeroFiberToParameterColimit_stage Stage sys i
  have hincl' := congrArg (fun f => f (family.toQCCR.point i)) hincl
  have hincl'' :
      qCcrParameterZeroFiberToParameterColimit Stage sys
          (qCcrParameterZeroFiberTopologicalInjection Stage sys i
            (family.toQCCR.point i)) =
        qCcrParameterTopologicalInjection Stage sys i
          (family.toQCCR.point i).1 := by
    simpa [qCcrParameterZeroFiberToParameterNatTrans] using hincl'
  have h := congrArg
    (fun z => qCcrParameterZeroFiberToParameterColimit Stage sys z) hpoint
  simpa [carCompatiblePointParameterColimitMap] using h.trans hincl''

end InfoGeometry.Canonical.CARCompatiblePointColimit
