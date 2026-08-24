/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2ArtinPresentation

/-!
# G₂ Artin-to-Weyl quotient bridge

The native presentation owner already supplies the quotient action
`coordinateAction : ArtinG2 →* Equiv.Perm G2CoordinateRoot`.  This owner
exposes its longest-element readback without introducing a second Weyl
carrier or a duplicate presentation.
-/

namespace InfoGeometry.Exceptional.G2ArtinWeylBridge

open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2ReducedWords

noncomputable section

theorem artinToWeyl_garside :
    coordinateAction G2ArtinPresentation.garside =
      dihedralToPerm
        InfoGeometry.Algebra.Zorn.G2LongestElementBridge.g2LongestNF := by
  exact G2ArtinPresentation.garsideWord_is_longest_readback

end

end InfoGeometry.Exceptional.G2ArtinWeylBridge
