import InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCl55WittEmbeddingBridge

/-!
# Exterior Hodge carrier into the `(5,5)` Witt carrier

This is a finite, carrier-level cross-tower bridge.  It composes the existing
finite exterior-to-split-coordinate equivalence with the existing `(4,4)` to
`(5,5)` Witt embedding.  The result transports the quadratic readout and all
endomorphism identities; it does not assert a Pin representation, an
exceptional-to-spin intertwiner, or compatibility with split-octonion
multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExteriorCl55CarrierBridge

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Lie.SplitOctonionCl55WittEmbeddingBridge

abbrev Exterior3 := InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev SplitCarrier :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.SplitOctonionCoordinateCarrier
abbrev V55 := InfoGeometry.Clifford.Clifford55.V55

/-- The composed exterior-to-`V55` linear carrier map. -/
def exteriorToV55 (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) : Exterior3 →ₗ[ℝ] V55 :=
  wittToV55Linear.comp e.toLinearMap

/-- The canonical retraction back to the exterior carrier. -/
def v55ToExterior (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) : V55 →ₗ[ℝ] Exterior3 :=
  e.symm.toLinearMap.comp v55ToWittLinear

@[simp] theorem exteriorToV55_apply
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (x : Exterior3) :
    exteriorToV55 e x = wittToV55 (e x) := rfl

@[simp] theorem v55ToExterior_exteriorToV55
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (x : Exterior3) :
    v55ToExterior e (exteriorToV55 e x) = x := by
  simp [v55ToExterior, exteriorToV55]

theorem exteriorToV55_injective
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    Function.Injective (exteriorToV55 e) := by
  intro x y hxy
  apply e.injective
  apply wittToV55Linear_injective
  exact hxy

/-- The exterior carrier sees the restricted `(5,5)` quadratic form through
the existing split-coordinate Witt norm. -/
theorem Q55_exteriorToV55
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (x : Exterior3) :
    Q55 (exteriorToV55 e x) = wittNorm (e x) := by
  exact Q55_wittToV55 (e x)

theorem exteriorToV55_transport_intertwines
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) (x : Exterior3) :
    exteriorToV55 e (T x) =
      wittToV55Linear (transportEnd e T (e x)) := by
  simp [exteriorToV55, transportEnd_apply]

theorem v55ToExterior_exteriorToV55_end
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) (x : Exterior3) :
    v55ToExterior e (wittToV55Linear (transportEnd e T (e x))) = T x := by
  simp [v55ToExterior, transportEnd_apply]

end InfoGeometry.Canonical.SplitOctonionExteriorCl55CarrierBridge
