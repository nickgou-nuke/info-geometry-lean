import InfoGeometry.Algebra.CuntzCantorSupergradedBridge
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

/-!
# Cuntz-SUSY connection via the five-graded superbracket closure

The Cuntz-Cantor binary word parity (`wordParityZ2` from
`CuntzCantorSupergradedBridge`) assigns parity 0 (even) or 1 (odd) to
binary words.  The `SuperTKKConformalClosure` routes the superbracket
`{Q,R}` according to the parity of `Q,R`:

* odd-odd (parity 1+1=0) → even-grade sector (gPosTwo or translation)
* odd-even → odd-grade sector (gNegOne or gPosOne)

The parity additivity `wordParityZ2 (u++v) = wordParityZ2 u + wordParityZ2 v`
from `wordParityZ2_append` is the algebraic form of this routing.

This file documents the connection; the actual routing theorems are in
`SuperTKKConformalClosure.`.
-/

namespace InfoGeometry.Algebra.CuntzSUSYFiveGradedBridge

/--
**Cuntz-Cantor word parity matches the superbracket routing.** The parity
additivity `wordParityZ2 (u++v) = wordParityZ2 u + wordParityZ2 v` from
`CuntzCantorSupergradedBridge.wordParityZ2_append` is claimed to be the
algebraic form of the superbracket routing in `SuperTKKConformalClosure`.

**Closure debt**: This theorem requires proving that the parity-additivity
identity implies the explicit gauge/routing described in the module docstring.
The routing theorems in `SuperTKKConformalClosure` may already cover this,
but the explicit implication has not been formalized as a named theorem
on this file's namespace.
-/
theorem word_parity_matches_superbracket_routing : True := by
  sorry

end InfoGeometry.Algebra.CuntzSUSYFiveGradedBridge
