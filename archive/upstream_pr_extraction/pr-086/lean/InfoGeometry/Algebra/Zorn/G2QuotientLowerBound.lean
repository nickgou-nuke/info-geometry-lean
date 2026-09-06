/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2GroupOrderReduction
import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-!
# Structural lower bound from the quotient injection

This owner isolates the cardinal arithmetic which turns a lower bound on the
concrete quotient by the unipotent subgroup into a lower bound on the ambient
automorphism group.  It does not assume quotient exhaustion.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientLowerBound

open InfoGeometry.Algebra.Zorn.G2GroupOrderReduction
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable instance : Fintype (SplitOctF2Aut ⧸ unipotentSubgroup) :=
  Fintype.ofFinite _

theorem nat_card_quotient_ge_189_of_fintype_card_ge_189
    [Fintype (SplitOctF2Aut ⧸ unipotentSubgroup)]
    (hq : 189 ≤ Fintype.card (SplitOctF2Aut ⧸ unipotentSubgroup)) :
    189 ≤ Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup) := by
  rw [Nat.card_eq_fintype_card]
  exact hq

theorem nat_card_ge_12096_of_quotient_ge_189
    (hq : 189 ≤ Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup)) :
    12096 ≤ Nat.card SplitOctF2Aut := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    unipotentSubgroup_card]
  calc
    12096 = 189 * 64 := by norm_num
    _ ≤ Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup) * 64 := by
      exact Nat.mul_le_mul_right 64 hq

end InfoGeometry.Algebra.Zorn.G2QuotientLowerBound
