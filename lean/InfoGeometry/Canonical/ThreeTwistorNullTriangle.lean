import InfoGeometry.Twistor.Incidence
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cyclic three-twistor null triangles

This owner packages three point pairs, each witnessed by a twistor incidence
relation.  The null edges are derived from the native finite soldering
theorem; no projective or manifold structure is assumed.
-/

namespace InfoGeometry.Canonical.ThreeTwistorNullTriangle

open InfoGeometry.Twistor.Incidence
open InfoGeometry.Clifford.Soldering

structure Data where
  X : Vec22
  Y : Vec22
  Z : Vec22
  twistorXY : Twistor
  twistorYZ : Twistor
  twistorZX : Twistor
  piXY_ne_zero : twistorXY.2 ≠ 0
  piYZ_ne_zero : twistorYZ.2 ≠ 0
  piZX_ne_zero : twistorZX.2 ≠ 0
  X_incident : Incident twistorXY X
  Y_incident : Incident twistorXY Y
  Y_incident_next : Incident twistorYZ Y
  Z_incident : Incident twistorYZ Z
  Z_incident_next : Incident twistorZX Z
  X_incident_next : Incident twistorZX X

theorem null_edge_XY (T : Data) :
    q22 (T.X - T.Y) = 0 := by
  exact incident_points_null_separated T.twistorXY T.X T.Y
    T.X_incident T.Y_incident T.piXY_ne_zero

theorem null_edge_YZ (T : Data) :
    q22 (T.Y - T.Z) = 0 := by
  exact incident_points_null_separated T.twistorYZ T.Y T.Z
    T.Y_incident_next T.Z_incident T.piYZ_ne_zero

theorem null_edge_ZX (T : Data) :
    q22 (T.Z - T.X) = 0 := by
  exact incident_points_null_separated T.twistorZX T.Z T.X
    T.Z_incident_next T.X_incident_next T.piZX_ne_zero

theorem cyclic_null_edges (T : Data) :
    q22 (T.X - T.Y) = 0 ∧
      q22 (T.Y - T.Z) = 0 ∧
        q22 (T.Z - T.X) = 0 := by
  exact ⟨null_edge_XY T, null_edge_YZ T, null_edge_ZX T⟩

end InfoGeometry.Canonical.ThreeTwistorNullTriangle
