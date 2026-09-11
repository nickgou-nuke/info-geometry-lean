/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2CircularRootComplement
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Exceptional.G2CircularRootComplementLabel

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Exceptional.G2CircularRootLabelTransport
open InfoGeometry.Exceptional.G2CircularRootComplement

abbrev RootLabel := G2CoordinateRoot

def complementRootLabel : Fin 4 → RootLabel
  | 0 => signedRootCoordinate (true, .alpha_add_beta)
  | 1 => signedRootCoordinate (true, .two_alpha_beta)
  | 2 => signedRootCoordinate (true, .three_alpha_beta)
  | 3 => signedRootCoordinate (true, .three_alpha_two_beta)

theorem complementRootLabel_injective :
    Function.Injective complementRootLabel := by
  intro i j h
  revert i j
  decide

theorem complementRootLabel_image :
    Finset.univ.image complementRootLabel = circularRootComplement := by
  native_decide

end InfoGeometry.Exceptional.G2CircularRootComplementLabel
