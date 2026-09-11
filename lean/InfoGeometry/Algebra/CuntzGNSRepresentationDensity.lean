import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace InfoGeometry.Algebra.CuntzGNSRepresentationDensity

open InfoGeometry.Algebra.CuntzNativeGNSBridge

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The Cuntz/GNS orbit map has dense range, specializing the generic native
GNS vacuum bridge. -/
theorem cuntzGNSRepresentation_denseRange (φ : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => cuntzGNSRepresentation φ a (gnsVacuum φ)) := by
  exact gnsVacuum_cyclic (φ := φ)

end InfoGeometry.Algebra.CuntzGNSRepresentationDensity
