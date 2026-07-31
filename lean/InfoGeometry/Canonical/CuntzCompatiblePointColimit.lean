import InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout

/-!
# Compatible Cuntz generator points in the q-CCR parameter colimit

For a C⋆-stage system, a coherent family of right-invertible Cuntz
generators gives a canonical point in the `q = 0` q-CCR fibre.  This owner
keeps the construction at the categorical `TopCat` colimit level; the
algebraic Fock left-regular realization can be related to it only after a
chosen C⋆ realization is supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCompatiblePointColimit

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {I : Type u} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

structure CompatibleCuntzPointFamily where
  c : ∀ i, Stage i
  cstar : ∀ i, Stage i
  relation : ∀ i, c i * cstar i = 1
  compatible_c : ∀ {i j : I} (hij : i ≤ j), sys.map hij (c i) = c j
  compatible_cstar : ∀ {i j : I} (hij : i ≤ j),
    sys.map hij (cstar i) = cstar j

def CompatibleCuntzPointFamily.toQCCR
    (family : CompatibleCuntzPointFamily sys) :
    CompatibleQCCRPointFamily sys where
  point i :=
    ⟨(family.c i, (family.cstar i, (0 : Stage i))), by
      change qCcrParameterResidualContinuousMap (A := Stage i)
          (family.c i, (family.cstar i, (0 : Stage i))) = 0
      simpa [qCcrParameterResidualContinuousMap] using
        qccr_to_cuntz_limit (family.c i) (family.cstar i) |>.2 (family.relation i)⟩
theorem CompatibleCuntzPointFamily.toQCCR_compatible
    (family : CompatibleCuntzPointFamily sys) :
    ∀ {i j : I} (hij : i ≤ j),
      qCcrParameterZeroFiberTransitionMap Stage sys hij
          (family.toQCCR.point i) = family.toQCCR.point j := by
    intro i j hij
    apply Subtype.ext
    change qCcrParameterTransitionMap Stage sys hij
        (family.c i, (family.cstar i, (0 : Stage i))) =
      (family.c j, (family.cstar j, (0 : Stage j)))
    simp [qCcrParameterTransitionMap, family.compatible_c hij,
      family.compatible_cstar hij]

noncomputable def cuntzCompatiblePointColimitMap
    (family : CompatibleCuntzPointFamily sys) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  compatiblePointColimitMap sys family.toQCCR
    family.toQCCR_compatible

theorem cuntzCompatiblePointColimitMap_stage_apply
    (family : CompatibleCuntzPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    cuntzCompatiblePointColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        (family.toQCCR.point i) := by
  exact compatiblePointColimitMap_stage_apply sys family.toQCCR
    family.toQCCR_compatible i u

noncomputable def cuntzCompatiblePointParameterColimitMap
    (family : CompatibleCuntzPointFamily sys) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  cuntzCompatiblePointColimitMap sys family ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem cuntzCompatiblePointParameterColimitMap_stage_apply
    (family : CompatibleCuntzPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    cuntzCompatiblePointParameterColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u) =
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
  simpa [cuntzCompatiblePointParameterColimitMap] using h.trans hincl''

end InfoGeometry.Canonical.CuntzCompatiblePointColimit
