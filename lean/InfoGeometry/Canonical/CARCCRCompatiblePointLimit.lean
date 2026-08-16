import InfoGeometry.Canonical.CARCompatiblePointColimit
import InfoGeometry.Canonical.CCRCompatiblePointColimit
import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit

/-!
# Inverse-limit readouts for compatible CAR and CCR witnesses

The CAR and CCR owners already descend compatible point families through the
direct q-CCR colimit.  This companion exposes the same families as cones over
the inverse `TopCat` diagram, so the finite witnesses have both universal
directions available.
-/

noncomputable section

namespace InfoGeometry.Canonical.CARCCRCompatiblePointLimit

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CARCompatiblePointColimit
open InfoGeometry.Canonical.CCRCompatiblePointColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {I : Type u} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

def carCompatiblePointTopCatFamily
    (family : CompatibleCARPointFamily sys) (i : I) :
    TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)} :=
  carParameterPointTopCatHom (family.c i) (family.cstar i)
    (family.relation i)

theorem carCompatiblePointTopCatFamily_natural
    (family : CompatibleCARPointFamily sys) {i j : I} (hij : i ≤ j) :
    carCompatiblePointTopCatFamily sys family i ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      carCompatiblePointTopCatFamily sys family j := by
  have h := carParameterPointTopCatHom_transition_natural sys hij
    (family.c i) (family.cstar i) (family.relation i)
  simpa [carCompatiblePointTopCatFamily,
    family.map_c hij, family.map_cstar hij] using h

noncomputable def carCompatiblePointLimitMap
    (family : CompatibleCARPointFamily sys) :
    TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys :=
  qCcrParameterZeroFiberPointLimitMap Stage sys
    (carCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact carCompatiblePointTopCatFamily_natural sys family (leOfHom f))

@[simp]
theorem carCompatiblePointLimitMap_projection
    (family : CompatibleCARPointFamily sys) (i : I) (u : PUnit) :
    limit.π
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
        (carCompatiblePointLimitMap sys family u) =
      carCompatiblePointTopCatFamily sys family i u := by
  exact qCcrParameterZeroFiberPointLimitMap_projection Stage sys
    (carCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact carCompatiblePointTopCatFamily_natural sys family (leOfHom f)) i u

noncomputable def carCompatiblePointAmbientLimitMap
    (family : CompatibleCARPointFamily sys) :
    TopCat.of PUnit ⟶ qCcrParameterTopologicalLimit Stage sys :=
  carCompatiblePointLimitMap sys family ≫
    qCcrParameterZeroFiberToParameterLimit Stage sys

@[simp]
theorem carCompatiblePointAmbientLimitMap_projection
    (family : CompatibleCARPointFamily sys) (i : I) (u : PUnit) :
    limit.π
        (qCcrParameterTopologicalDiagram Stage sys) i
        (carCompatiblePointAmbientLimitMap sys family u) =
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i
        (carCompatiblePointTopCatFamily sys family i u) := by
  have h := qCcrParameterZeroFiberPointAmbientLimitMap_projection
    Stage sys (carCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact carCompatiblePointTopCatFamily_natural sys family (leOfHom f)) i u
  simpa [carCompatiblePointAmbientLimitMap, carCompatiblePointLimitMap] using h

def ccrCompatiblePointTopCatFamily
    (family : CompatibleCCRPointFamily sys) (i : I) :
    TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)} :=
  ccrParameterPointTopCatHom (family.c i) (family.cstar i)
    (family.relation i)

theorem ccrCompatiblePointTopCatFamily_natural
    (family : CompatibleCCRPointFamily sys) {i j : I} (hij : i ≤ j) :
    ccrCompatiblePointTopCatFamily sys family i ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      ccrCompatiblePointTopCatFamily sys family j := by
  have h := ccrParameterPointTopCatHom_transition_natural sys hij
    (family.c i) (family.cstar i) (family.relation i)
  simpa [ccrCompatiblePointTopCatFamily,
    family.map_c hij, family.map_cstar hij] using h

noncomputable def ccrCompatiblePointLimitMap
    (family : CompatibleCCRPointFamily sys) :
    TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys :=
  qCcrParameterZeroFiberPointLimitMap Stage sys
    (ccrCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact ccrCompatiblePointTopCatFamily_natural sys family (leOfHom f))

@[simp]
theorem ccrCompatiblePointLimitMap_projection
    (family : CompatibleCCRPointFamily sys) (i : I) (u : PUnit) :
    limit.π
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
        (ccrCompatiblePointLimitMap sys family u) =
      ccrCompatiblePointTopCatFamily sys family i u := by
  exact qCcrParameterZeroFiberPointLimitMap_projection Stage sys
    (ccrCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact ccrCompatiblePointTopCatFamily_natural sys family (leOfHom f)) i u

noncomputable def ccrCompatiblePointAmbientLimitMap
    (family : CompatibleCCRPointFamily sys) :
    TopCat.of PUnit ⟶ qCcrParameterTopologicalLimit Stage sys :=
  ccrCompatiblePointLimitMap sys family ≫
    qCcrParameterZeroFiberToParameterLimit Stage sys

@[simp]
theorem ccrCompatiblePointAmbientLimitMap_projection
    (family : CompatibleCCRPointFamily sys) (i : I) (u : PUnit) :
    limit.π
        (qCcrParameterTopologicalDiagram Stage sys) i
        (ccrCompatiblePointAmbientLimitMap sys family u) =
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i
        (ccrCompatiblePointTopCatFamily sys family i u) := by
  have h := qCcrParameterZeroFiberPointAmbientLimitMap_projection
    Stage sys (ccrCompatiblePointTopCatFamily sys family)
    (by
      intro i j f
      exact ccrCompatiblePointTopCatFamily_natural sys family (leOfHom f)) i u
  simpa [ccrCompatiblePointAmbientLimitMap, ccrCompatiblePointLimitMap] using h

end InfoGeometry.Canonical.CARCCRCompatiblePointLimit
