import InfoGeometry.Canonical.CoordinateFree
import InfoGeometry.Canonical.ZetaTraceBridge
import InfoGeometry.Canonical.BerryRotorBridge
import InfoGeometry.Canonical.ZetaTrace
import InfoGeometry.Canonical.ModularBerryBridge

namespace InfoGeometry.Canonical.DiscreteModularSpectrumCoordinateFree

/--
Compatibility surface for the older discrete coordinate-free lane.

The file is now folded into the chart-free contract:
- `CoordinateFree` names the API contract.
- the arithmetic and modular bridges live in the normalized canonical modules.
- the discrete modular spectrum language remains available only as a thin
  compatibility namespace.
-/
def CoordinateFreeContract : Prop := InfoGeometry.Canonical.CoordinateFreeContract

/-- The coordinate-free contract holds in the compatibility namespace. -/
theorem coordinateFreeContract : CoordinateFreeContract :=
  InfoGeometry.Canonical.coordinateFreeContract

end InfoGeometry.Canonical.DiscreteModularSpectrumCoordinateFree
