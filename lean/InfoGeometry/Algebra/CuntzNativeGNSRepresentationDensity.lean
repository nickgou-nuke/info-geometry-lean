import InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Density of the native GNS cyclic representation

This is the topological readout of cyclicity: the algebra orbit of the vacuum
is dense in the completed Mathlib GNS space.  No topology is imposed on the
algebraic Cuntz quotient itself.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace InfoGeometry.Algebra.CuntzNativeGNSRepresentationDensity

open InfoGeometry.Algebra.CuntzNativeGNSBridge

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →ₚ[ℂ] ℂ)

theorem gnsVacuum_denseRange :
    DenseRange (fun a : A => cuntzGNSRepresentation φ a (gnsVacuum φ)) := by
  exact gnsVacuum_cyclic φ

theorem gnsVacuum_range_closure_eq_univ :
    closure (Set.range (fun a : A => cuntzGNSRepresentation φ a (gnsVacuum φ))) =
      Set.univ := by
  exact (denseRange_iff_closure_range.mp (gnsVacuum_denseRange φ))

theorem gnsVacuum_mem_closure_range :
    gnsVacuum φ ∈
      closure (Set.range (fun a : A => cuntzGNSRepresentation φ a (gnsVacuum φ))) := by
  rw [gnsVacuum_range_closure_eq_univ φ]
  simp

end InfoGeometry.Algebra.CuntzNativeGNSRepresentationDensity
