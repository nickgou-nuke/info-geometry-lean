/-
InfoGeometry/Canonical/TomitaFisherMetric.lean

The former contents were a diagonal `M₂(ℝ)` Fisher seed evaluated at two
scalar channels.  That is a coordinate toy, not the Fisher metric of a
noncommutative state on an observable algebra.

The native replacement is
`CoordinatelessSouriauKMSBridge.QuantumFisherSLDMetric`, whose metric is
carried by observables and a state functional.  Its operatorial state/
SLD-product theorems are the authoritative Fisher/KMS interface.

This file is an import-routing marker only.  It exports no diagonal matrix
API and makes no Tomita or Fisher theorem claim of its own.
-/

import InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge

namespace InfoGeometry.Canonical.TomitaFisherMetric

/- The former diagonal finite seed is retired; use the native SLD owner. -/

end InfoGeometry.Canonical.TomitaFisherMetric
