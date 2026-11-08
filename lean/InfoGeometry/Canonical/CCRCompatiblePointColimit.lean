import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
      dsimp [qCcrParameterZeroLocus, qCcrParameterResidualContinuousMap, ccrParameterPoint]
      exact ccr_is_plus_one_qccr (family.c i) (family.cstar i) (family.relation i)⟩
  compatible := by
    intro i j hij
    apply Subtype.ext
    change (sys.map hij (family.c i),
        (sys.map hij (family.cstar i), sys.map hij (1 : Stage i))) =
      (family.c j, (family.cstar j, (1 : Stage j)))
    simp [family.compatible_c hij, family.compatible_cstar hij]

noncomputable def ccrCompatiblePointColimitMap
    (family : CompatibleCCRPointFamily sys) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  compatiblePointColimitMap sys family.toQCCR

theorem ccrCompatiblePointColimitMap_stage_apply
    (family : CompatibleCCRPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    ccrCompatiblePointColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys i
        (family.toQCCR.point i) := by
  exact compatiblePointColimitMap_stage_apply sys family.toQCCR i u

noncomputable def ccrCompatiblePointParameterColimitMap
    (family : CompatibleCCRPointFamily sys) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  ccrCompatiblePointColimitMap sys family ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

theorem ccrCompatiblePointParameterColimitMap_stage_apply
    (family : CompatibleCCRPointFamily sys) (i : I) (u : PUnit.{u + 1}) :
    ccrCompatiblePointParameterColimitMap sys family
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
      (ccrCompatiblePointColimitMap sys family
        (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i u)) =
    qCcrParameterTopologicalInjection Stage sys i (family.toQCCR.point i).1
  rw [ccrCompatiblePointColimitMap_stage_apply]
  exact hincl'

end InfoGeometry.Canonical.CCRCompatiblePointColimit
