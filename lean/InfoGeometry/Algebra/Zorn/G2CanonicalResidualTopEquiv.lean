/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2BruhatResidualCanonicalEquiv
import InfoGeometry.Algebra.Zorn.G2TopOrderedRootProduct
import InfoGeometry.Algebra.Zorn.G2BruhatResidual

/-!
# Canonical top product-image equivalence

The top-cell ordered-product equivalence is stated on the Bruhat residual
fiber.  This file transports it to the canonical residual fiber using the
already proved carrier equivalence.  No new subgroup parametrisation is
asserted for intermediate Weyl elements.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualTopEquiv

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2BruhatResidualCanonicalEquiv
open InfoGeometry.Algebra.Zorn.G2TopOrderedRootProduct
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2ReducedWords

noncomputable def canonicalTopResidualEquiv :
    CanonicalResidualExponent (weylElementOfNF (3, false)) ≃
      residualSubgroup (3, false) :=
  (bruhatResidualToCanonical (3, false)).symm.trans
    topOrderedRootProductEquiv

theorem canonicalTopResidual_card :
    Nat.card (CanonicalResidualExponent (weylElementOfNF (3, false))) =
      Nat.card (residualSubgroup (3, false)) :=
  Nat.card_congr canonicalTopResidualEquiv

theorem canonicalTopResidual_card_eq_sixtyFour :
    Nat.card (CanonicalResidualExponent (weylElementOfNF (3, false))) = 64 := by
  rw [canonicalTopResidual_card]
  exact residualSubgroup_top_parameter_card

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualTopEquiv
