/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2ResidualFiberTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords

/-!
# Six-bit coordinate readout for the canonical residual fiber

The canonical residual fiber has five remaining basis positions, but its
first two upper Peirce vectors are supported on three coordinates each.  The
resulting six Boolean coordinates are the correct carrier-level counterpart
of the six positive-root bits in the longest Weyl residual exponent.

This owner deliberately proves the coordinate injection only.  Surjectivity
requires the separate concrete constraint-to-PC-word alignment theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualFiberCoordinate

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints
open InfoGeometry.Algebra.Zorn.G2PeirceFibration
open InfoGeometry.Algebra.Zorn.G2ResidualFiberTransport
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def residualFiberSixBits
    (v : ResidualFiber canonicalP canonicalX) : Fin 6 → Bool :=
  residualUpperPairBits (residualUpperPairOfFiberCarrier v)

noncomputable def residualFiberToW0Exponent
    (v : ResidualFiber canonicalP canonicalX) :
    CanonicalResidualExponent G2WeylElement.w0 :=
  (canonicalResidualBinaryEquiv G2WeylElement.w0).symm
    (residualFiberSixBits v)

theorem residualFiberSixBits_injective :
    Function.Injective residualFiberSixBits := by
  intro v w h
  have hbits :
      residualUpperPairBits (residualUpperPairOfFiberCarrier v) =
        residualUpperPairBits (residualUpperPairOfFiberCarrier w) := by
    simpa [residualFiberSixBits] using h
  have hpairs :
      residualUpperPairOfFiberCarrier v =
        residualUpperPairOfFiberCarrier w :=
    residualUpperPairBits_injective_of_ePlus canonicalP_value hbits
  apply residualFiberUpperPair_injective
  simpa [residualUpperPairOfFiberCarrier, residualUpperPairOfFiber,
    residualFiberUpperPair] using hpairs

theorem residualFiberToW0Exponent_injective :
    Function.Injective residualFiberToW0Exponent := by
  intro v w h
  apply residualFiberSixBits_injective
  exact (canonicalResidualBinaryEquiv G2WeylElement.w0).symm.injective h

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualFiberCoordinate
