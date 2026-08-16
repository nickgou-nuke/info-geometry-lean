/-
InfoGeometry/OperatorAlgebra/BoundaryFiveGradingShadow.lean

The former contents of this module were a finite `Matrix (Fin n) ... ℤ`
shadow proved by `decide`.  They were not a representation of the operator
algebraic boundary and had no Lean consumers in the maintained source tree.

The native owners are deliberately kept separate:

* `GeneralizedNilpotentTripotent` owns tripotent operators and their
  plus/minus/null projectors on modules;
* `Physics.Algebra.TripotentFiveGradingDecomposition` and
  `SuperTKKConformalClosure` own typed five-grade ranges and bracket laws;
* `ModularSignCPT` owns the real doubled-space sign/CPT/Krein relations.

This file is an import-routing marker only.  It exports no scalar matrix
replacement API and does not claim the O(5,5)/Pin(5,5) bulk theorem.
-/

import InfoGeometry.OperatorAlgebra.GeneralizedNilpotentTripotent
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

namespace InfoGeometry.OperatorAlgebra.BoundaryFiveGradingShadow

/- The former finite matrix shadow is retired; use the native owners named in
the module documentation above. -/

end InfoGeometry.OperatorAlgebra.BoundaryFiveGradingShadow
