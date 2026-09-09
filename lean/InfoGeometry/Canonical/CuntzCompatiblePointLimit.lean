import InfoGeometry.Canonical.CuntzCompatiblePointColimit
import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit

/-!
# Inverse-limit readouts for compatible Cuntz witnesses

The compatible Cuntz point family already descends to the filtered q-CCR
zero-fibre colimit.  This owner supplies the dual inverse-limit cone and its
ambient parameter readout using the native `TopCat` limit construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCompatiblePointLimit

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
open InfoGeometry.Canonical.CuntzCompatiblePointColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {I : Type u} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

def cuntzCompatiblePointTopCatFamily
    (family : CompatibleCuntzPointFamily sys) (i : I) :
    TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)} :=
  TopCat.ofHom
    { toFun := fun _ => family.toQCCR.point i
      continuous_toFun := continuous_const }

theorem cuntzCompatiblePointTopCatFamily_natural
    (family : CompatibleCuntzPointFamily sys) {i j : I} (hij : i ≤ j) :
    cuntzCompatiblePointTopCatFamily sys family i ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      cuntzCompatiblePointTopCatFamily sys family j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  exact congrArg Subtype.val (family.toQCCR.compatible hij)

noncomputable def cuntzCompatiblePointLimitMap
    (family : CompatibleCuntzPointFamily sys) :
    TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys :=
  qCcrParameterZeroFiberPointLimitMap Stage sys
    (cuntzCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact cuntzCompatiblePointTopCatFamily_natural sys family (leOfHom f))

@[simp]
theorem cuntzCompatiblePointLimitMap_projection
    (family : CompatibleCuntzPointFamily sys) (i : I) (u : PUnit) :
    topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
        (cuntzCompatiblePointLimitMap sys family u) =
      cuntzCompatiblePointTopCatFamily sys family i u := by
  exact qCcrParameterZeroFiberPointLimitMap_projection Stage sys
    (cuntzCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact cuntzCompatiblePointTopCatFamily_natural sys family (leOfHom f)) i u

noncomputable def cuntzCompatiblePointAmbientLimitMap
    (family : CompatibleCuntzPointFamily sys) :
    TopCat.of PUnit ⟶ qCcrParameterTopologicalLimit Stage sys :=
  cuntzCompatiblePointLimitMap sys family ≫
    qCcrParameterZeroFiberToParameterLimit Stage sys

@[simp]
theorem cuntzCompatiblePointAmbientLimitMap_projection
    (family : CompatibleCuntzPointFamily sys) (i : I) (u : PUnit) :
    topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i
        (cuntzCompatiblePointAmbientLimitMap sys family u) =
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i
        (cuntzCompatiblePointTopCatFamily sys family i u) := by
  have h := qCcrParameterZeroFiberPointAmbientLimitMap_projection
    Stage sys (cuntzCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact cuntzCompatiblePointTopCatFamily_natural sys family (leOfHom f)) i u
  simpa [cuntzCompatiblePointAmbientLimitMap,
    cuntzCompatiblePointLimitMap] using h

end InfoGeometry.Canonical.CuntzCompatiblePointLimit
