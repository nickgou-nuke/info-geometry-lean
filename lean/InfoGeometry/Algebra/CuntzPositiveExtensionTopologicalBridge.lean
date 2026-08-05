import InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge

/-!
# Topological readout of a represented algebraic Cuntz quotient

Given a positive C*-extension of the algebraic quotient, each quotient element
acts by a genuine continuous GNS operator.  The quotient itself remains an
algebraic parameter; no unsupported quotient topology is introduced here.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open CategoryTheory

namespace InfoGeometry.Algebra.CuntzPositiveExtensionTopologicalBridge

open InfoGeometry.Algebra.CuntzNativeGNSBridge
open InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge
open InfoGeometry.Algebra.CuntzTensorQuotient

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def representedCuntzOperatorTopCat
    {n : ℕ} (E : CuntzPositiveExtension n A) (x : CuntzAlg n) :
    TopCat.of E.phi.GNS ⟶ TopCat.of E.phi.GNS :=
  gnsOperatorTopCat E.phi (E.representation.toAlgHom x)

@[simp] theorem representedCuntzOperatorTopCat_apply
    {n : ℕ} (E : CuntzPositiveExtension n A) (x : CuntzAlg n)
    (v : E.phi.GNS) :
    representedCuntzOperatorTopCat E x v =
      cuntzGNSRepresentation E.phi
        (E.representation.toAlgHom x) v := by
  rfl

theorem representedCuntzOperatorTopCat_continuous
    {n : ℕ} (E : CuntzPositiveExtension n A) (x : CuntzAlg n) :
    Continuous (cuntzGNSRepresentation E.phi
      (E.representation.toAlgHom x)) := by
  exact gnsOperatorTopCat_continuous E.phi (E.representation.toAlgHom x)

theorem representedCuntz_expectation_recovery
    {n : ℕ} (E : CuntzPositiveExtension n A) (x : CuntzAlg n) :
    ⟪gnsVacuum E.phi,
      representedCuntzOperatorTopCat E x (gnsVacuum E.phi)⟫_ℂ = E.omega x := by
  simpa [representedCuntzOperatorTopCat] using
    (represented_cuntz_expectation_recovery E x)

end InfoGeometry.Algebra.CuntzPositiveExtensionTopologicalBridge
