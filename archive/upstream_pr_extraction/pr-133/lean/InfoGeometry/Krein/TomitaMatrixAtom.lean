/-
InfoGeometry/Krein/TomitaMatrixAtom.lean

The former contents were a concrete `2 × 2` real matrix atom.  That finite
coordinate shadow is retired: it is not the Tomita operator of a standard
form and it is not the noncommutative Krein carrier.

Use the native owners instead:

* `Canonical.TomitaTakesaki` and `Canonical.TomitaTakesakiModularFlow` for
  Tomita/modular data;
* `Quantum.RealSplitClifford` and `Quantum.RealMajoranaCategory` for the
  real Clifford/CAR carrier;
* `OperatorAlgebra.ModularSignCPT` for typed sign, CPT, and Hestenes phase
  relations;
* `OperatorAlgebra.RealDoubledChiralKreinModularBridge` for their doubled
  carrier assembly.

This marker exports no matrix replacement API and makes no analytic or
infinite-dimensional Tomita claim.
-/

import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TomitaTakesakiModularFlow
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinModularBridge
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Quantum.RealSplitClifford

namespace InfoGeometry.Krein.TomitaMatrixAtom

/- The former finite matrix atom is retired; use the native owners above. -/

end InfoGeometry.Krein.TomitaMatrixAtom
