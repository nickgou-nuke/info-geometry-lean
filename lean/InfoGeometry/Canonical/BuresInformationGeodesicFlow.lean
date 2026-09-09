import InfoGeometry.External.Auto.BuresInformationGeodesicFlow
import InfoGeometry.Canonical.BuresMetricClosedCartography

/-!
# Canonical Bures information-geodesic flow owner

Compatibility-only canonical import surface for the finite Bures/Fisher/modular
packet recovered from external auto and archive surfaces.

The authoritative finite theorem content currently remains in
`InfoGeometry.External.Auto.BuresInformationGeodesicFlow`; this maintained owner
re-homes the import boundary without restating the external declarations until
their exported namespace surface is normalized.
-/

noncomputable section

namespace InfoGeometry.Canonical.BuresInformationGeodesicFlow

/-- Canonical re-export of the finite Bures center-distance theorem from the
authoritative restored owner. -/
theorem canonical_bures_center_distance_zero :
    BuresInformationGeodesicFlow.buresDistance 0 0 0 0 0 0 = 0 :=
  BuresInformationGeodesicFlow.bures_center_distance_zero

end InfoGeometry.Canonical.BuresInformationGeodesicFlow

end noncomputable section
