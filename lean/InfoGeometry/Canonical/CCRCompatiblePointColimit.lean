import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
import InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit

/-!
# Compatible CCR witnesses in the filtered q-CCR zero-fiber colimit

This is the commutator-sign counterpart of the CAR witness descent.  The
finite relation and its transition compatibility are carried into the common
noncommutative q-CCR zero-fiber colimit through the generic `TopCat` map.
-/

noncomputable section

namespace InfoGeometry.Canonical.CCRCompatiblePointColimit

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

structure CompatibleCCRPointFamily where
  c : ∀ i, Stage i
  cstar : ∀ i, Stage i
  relation : ∀ i, c i * cstar i - cstar i * c i = 1
  compatible_c : ∀ {i j : I} (hij : i ≤ j), sys.map hij (c i) = c j
  compatible_cstar : ∀ {i j : I} (hij : i ≤ j),
    sys.map hij (cstar i) = cstar j

def CompatibleCCRPointFamily.toQCCR
    (family : CompatibleCCRPointFamily sys) :
    CompatibleQCCRPointFamily sys where
  point i :=
    ⟨ccrParameterPoint (family.c i) (family.cstar i), by
      change qCcrParameterResidualContinuousMap (A := Stage i)
          (ccrParameterPoint (family.c i) (family.cstar i)) = 0
      simpa [qCcrParameterResidualContinuousMap, ccrParameterPoint] using
        ccr_is_plus_one_qccr (family.c i) (family.cstar i) (family.relation i)⟩
theorem CompatibleCCRPointFamily.toQCCR_compatible
    (family : CompatibleCCRPointFamily sys) :
    ∀ {i j : I} (hij : i ≤ j),
      qCcrParameterZeroFiberTransitionMap Stage sys hij
          (family.toQCCR.point i) = family.toQCCR.point j := by
    intro i j hij
    apply Subtype.ext
    change qCcrParameterTransitionMap Stage sys hij
        (ccrParameterPoint (family.c i) (family.cstar i)) =
      ccrParameterPoint (family.c j) (family.cstar j)
    simp [qCcrParameterTransitionMap, ccrParameterPoint,
      family.compatible_c hij, family.compatible_cstar hij]

noncomputable def ccrCompatiblePointColimitMap
    (family : CompatibleCCRPointFamily sys) :
    colimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  compatiblePointColimitMap sys family.toQCCR
    family.toQCCR_compatible

theorem ccrCompatiblePointColimitMap_stage_apply
    (family : CompatibleCCRPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    ccrCompatiblePointColimitMap sys family
        (colimit.ι ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        (family.toQCCR.point i) := by
  exact compatiblePointColimitMap_stage_apply sys family.toQCCR
    family.toQCCR_compatible i u

noncomputable def ccrCompatiblePointParameterColimitMap
    (family : CompatibleCCRPointFamily sys) :
    colimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  ccrCompatiblePointColimitMap sys family ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem ccrCompatiblePointParameterColimitMap_stage_apply
    (family : CompatibleCCRPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    ccrCompatiblePointParameterColimitMap sys family
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
  simpa [ccrCompatiblePointParameterColimitMap] using h.trans hincl''

end InfoGeometry.Canonical.CCRCompatiblePointColimit
