/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.PenroseBitwistorSplitOctonion
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Twistor.PenroseCanonicalZornSoldering
import InfoGeometry.Twistor.PenroseZornWittBoundary

/-!
# Penrose dimension and circular-carrier bridge

This owner records only the dimension-level compatibility between Penrose's
bi-twistor carrier and the existing circular split-octonion carrier.  It does
not assert an identification of metrics, products, twistor incidence, or
`G₂` representations.
-/

namespace InfoGeometry.Algebra.PenroseTwistorG2

open InfoGeometry.Algebra.PenroseTwistorG2.BiTwistorSpace
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Twistor.PenroseCanonicalZornSoldering
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Twistor.PenroseZornWittBoundary

theorem penrose_dimension_matches_circular_carrier :
    biTwistorSpaceDim = Module.finrank ℝ CartesianCoordinates := by
  rw [cartesianCoordinates_finrank]
  rfl

theorem penrose_dimension_split_matches_circular_carrier :
    1 + imaginaryVectorSpaceDim = Module.finrank ℝ CartesianCoordinates := by
  rw [penrose_dimension_split_eq_8, cartesianCoordinates_finrank]
  rfl

/-- The four-plane operator carrier has the same eight labels as the Penrose
bi-twistor dimension.  This is only a cardinality statement; it supplies no
identification of the operator carrier with the Penrose product. -/
theorem penrose_dimension_matches_four_plane_labels :
    biTwistorSpaceDim = Fintype.card (Fin 4 × Fin 2) := by
  simp [biTwistorSpaceDim]

/-- The existing realification has an explicit circular-coordinate readback.
This is carrier transport only; it does not preserve the Penrose product. -/
theorem penrose_circular_coordinates_readback (z : TwistorCarrier) :
    circularPeirceBasis.equivFun (penroseCanonicalZornEquiv z) =
      penroseRealPeirceEquiv z := by
  exact penroseCanonicalZornEquiv_circularCoordinates z

theorem penrose_circular_basis_readback (i : Fin 8) :
    penroseCanonicalZornEquiv
        (penroseRealPeirceEquiv.symm (Pi.single i 1)) =
      circularPeirceBasis i := by
  exact penroseCanonicalZornEquiv_circularBasis i

theorem penrose_circular_transport_eq_zero_iff (z : TwistorCarrier) :
    penroseCanonicalZornEquiv z = 0 ↔ z = 0 := by
  exact penroseCanonicalZornEquiv.map_eq_zero_iff

theorem penrose_witt_zorn_norm_readback
    (Z : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
      (penroseWittZornMap Z) =
      penroseRealSplitSignature Z := by
  exact penroseWittZorn_norm_eq_splitSignature Z

theorem penrose_quadratic_witt_zorn_compatibility
    (Z : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    twistorRealQuadraticForm (penroseTwistor4CarrierEquiv Z) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (penroseWittZornMap Z) := by
  exact penroseTwistor4Carrier_quadratic_eq_wittZorn_norm Z

theorem penrose_witt_null_iff_zorn_null
    (Z : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    penroseRealSplitSignature Z = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (penroseWittZornMap Z) = 0 := by
  exact penrose_split_null_iff_zorn_null Z

end InfoGeometry.Algebra.PenroseTwistorG2
