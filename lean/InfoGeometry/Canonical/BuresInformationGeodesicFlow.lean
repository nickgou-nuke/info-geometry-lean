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

/-- Compatibility owner marker for the restored Bures information-geodesic lane. -/
def canonicalOwnerMarker : Prop := True

theorem canonicalOwnerMarker_true : canonicalOwnerMarker := by
  trivial

end InfoGeometry.Canonical.BuresInformationGeodesicFlow

end noncomputable section
