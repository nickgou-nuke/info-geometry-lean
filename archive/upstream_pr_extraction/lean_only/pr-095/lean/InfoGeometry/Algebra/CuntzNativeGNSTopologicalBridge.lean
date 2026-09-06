import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.CuntzNativeGNSBridge

/-!
# Topological readout of the native GNS representation

The positive-functional GNS construction already produces a Hilbert completion.
This file exposes each represented algebra element as a genuine morphism in
`TopCat`; it does not add a topology to the algebraic Cuntz tensor quotient.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge

open CategoryTheory
open InfoGeometry.Algebra.CuntzNativeGNSBridge

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →ₚ[ℂ] ℂ)

noncomputable def gnsOperatorTopCat (a : A) :
    TopCat.of φ.GNS ⟶ TopCat.of φ.GNS :=
  TopCat.ofHom
    { toFun := cuntzGNSRepresentation φ a
      continuous_toFun := (cuntzGNSRepresentation φ a).cont }

@[simp] theorem gnsOperatorTopCat_apply (a : A) (x : φ.GNS) :
    gnsOperatorTopCat φ a x = cuntzGNSRepresentation φ a x := by
  rfl

theorem gnsOperatorTopCat_continuous (a : A) :
    Continuous (cuntzGNSRepresentation φ a) := by
  exact (cuntzGNSRepresentation φ a).cont

theorem gnsOperatorTopCat_one :
    gnsOperatorTopCat φ (1 : A) = 𝟙 (TopCat.of φ.GNS) := by
  apply TopCat.hom_ext
  ext x
  simp [gnsOperatorTopCat]

end InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge
