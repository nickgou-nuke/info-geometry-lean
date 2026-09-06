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

open InfoGeometry.Algebra.CuntzCantorSupergradedBridge
open InfoGeometry.Algebra.SupergradedSUSY

/--
The finite theorem-backed routing packet available in this file: two odd
Cuntz-Cantor one-bit steps compose to even parity, and the finite SUSY matrix
shadow has `{Q,Q}=2P_x`.
-/
theorem word_parity_matches_superbracket_routing (a b : Bool) :
    wordParityZ2 (oddStep a) = 1 ∧
      wordParityZ2 (oddStep b) = 1 ∧
        wordParityZ2 (oddStep a ++ oddStep b) = 0 ∧
          superAnticommutator Q Q = P_x + P_x := by
  exact cuntz_odd_odd_generates_even_translation_packet a b

end InfoGeometry.Algebra.CuntzSUSYFiveGradedBridge
