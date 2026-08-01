import InfoGeometry.Krein.HestenesJonesFiltrationBridge
import InfoGeometry.Canonical.WeylGWVolumeBridge

/-!
This module is an import boundary only.

The former `Bridge` structure duplicated two existing owners and stored their
shared `omegaVolume` equality as an unevaluated evidence field.  The actual
Jones-filtration and Weyl/GW volume theorems are owned by the imported
modules; downstream code should use those owners directly.
-/
