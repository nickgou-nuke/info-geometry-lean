import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Finite Gromov probability atoms in canonical mathlib notation

This module records finite counting facts directly with `Finset.card`,
intersection, Cartesian product, `Nat.factorial`, and rational division.  It
introduces no local wrappers for measure, projection, permutation count, or
normalized probability.

No analytic limit, Taylor expansion, Stirling bound, concentration theorem, or
symmetric-group quotient is asserted.
-/

set_option autoImplicit false

namespace GromovProbability

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Scaling the secondary rational readout by total cardinality recovers the intersection count. -/
theorem normalization_secondary (A B : Finset α) (h : A.card ≠ 0) :
    (if A.card = 0 then 0 else ((A ∩ B).card : ℚ) / (A.card : ℚ)) * (A.card : ℚ) =
      ((A ∩ B).card : ℚ) := by
  split_ifs with h_zero
  · exact False.elim (h h_zero)
  · exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

end GromovProbability
