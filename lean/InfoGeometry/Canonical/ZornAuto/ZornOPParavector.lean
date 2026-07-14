import InfoGeometry.External.Auto.ZornOPParavector

/-!
# Canonical compatibility shim for the Zorn OP paravector layer

The canonical Zorn triality/TKK bridge expects this module path, while the
implementation currently lives under `InfoGeometry.External.Auto`.  This file
forwards the import so the canonical dependency chain can resolve without
duplicating the owner.
-/
