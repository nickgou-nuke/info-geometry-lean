import InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
import InfoGeometry.Projective.KleinQuadricCarrierEquiv

/-!
# Exterior Klein incidence in the twistor Pluecker carrier

This owner transports the coordinate-free two-plane incidence theorem to the
existing `KleinQuadricPlucker` carrier used by the twistor/Grassmannian lane.
It introduces no new geometric carrier.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinTwistorIncidence

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
open InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
open InfoGeometry.Projective.KleinQuadricCarrierEquiv

/-- The native function-space four-vector read in the established twistor
coordinate carrier. -/
def twistorCoordinateVec4 (u : Vec4) :
    InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ where
  x0 := u I4.t
  x1 := u I4.x
  x2 := u I4.y
  x3 := u I4.z

@[simp] theorem plucker6Equiv_linePlucker (u v : Vec4) :
    plucker6Equiv ℝ (linePlucker u v) =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine
        (twistorCoordinateVec4 u) (twistorCoordinateVec4 v) := by
  rfl

/-- Plane incidence is exactly vanishing of the Klein polar pairing in the
same six-coordinate carrier used by the twistor/Grassmannian owners. -/
theorem kleinIncident_iff_twistor_kleinPolar
    (uv st : NondegenerateExteriorFrame) :
    KleinIncident (frameToKleinLocus uv) (frameToKleinLocus st) ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine
          (twistorCoordinateVec4 (uv.1 0)) (twistorCoordinateVec4 (uv.1 1)))
        (InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine
          (twistorCoordinateVec4 (st.1 0)) (twistorCoordinateVec4 (st.1 1))) = 0 := by
  rw [kleinIncident_iff_coordinate_incidence,
    incidenceForm_eq_kleinPolar,
    plucker6Equiv_linePlucker, plucker6Equiv_linePlucker]

end InfoGeometry.Projective.ExteriorKleinTwistorIncidence
