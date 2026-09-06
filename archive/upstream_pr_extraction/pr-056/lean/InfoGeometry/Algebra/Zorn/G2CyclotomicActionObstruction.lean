/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge

/-!
# Boundary of the sectorwise cyclotomic model

The existing cyclotomic action uses the same reflection axis in both sectors.
The concrete signed G₂ reflection does not have that property, so an
equivariant identification with this action must not be asserted.
-/

namespace InfoGeometry.Algebra.Zorn.G2CyclotomicActionObstruction

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl

def s1Signed : Bool × G2PositiveRoot → Bool × G2PositiveRoot
  | (b, .alpha) => (!b, .alpha)
  | (b, .beta) => (b, .three_alpha_beta)
  | (b, .alpha_add_beta) => (b, .two_alpha_beta)
  | (b, .two_alpha_beta) => (b, .alpha_add_beta)
  | (b, .three_alpha_beta) => (b, .beta)
  | (b, .three_alpha_two_beta) => (b, .three_alpha_two_beta)

theorem no_dihedral_equivariance_for_s1 :
    ¬ ∃ g : DihedralGroup 6, ∀ r : Bool × G2PositiveRoot,
      signedCyclotomic (s1Signed r) = g • signedCyclotomic r := by
  classical
  decide

end InfoGeometry.Algebra.Zorn.G2CyclotomicActionObstruction
