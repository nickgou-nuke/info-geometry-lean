/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceParityClosure

/-!
# Exact sign conditions for Peirce parity

Contract: use the native `grading`, `evenPart`, and `oddPart` in an arbitrary
associative ring. The identities follow from `two_nsmul_evenPart` and
`two_nsmul_oddPart`; even idempotency is unnecessary for these two algebraic
equivalences. No cancellation of two or identification of sign eigenspaces
with Peirce components is asserted.
-/

namespace InfoGeometry.Algebra.PeirceDeWittChiralSplit

variable {A : Type*} [Ring A]

/-- The precise obstruction to recovering even parity from a positive sign. -/
theorem grading_conjugation_fixed_iff_odd_two_torsion (p x : A) :
    grading p * x * grading p = x ↔ (2 : ℕ) • oddPart p x = 0 := by
  rw [two_nsmul_oddPart, sub_eq_zero, eq_comm]

/-- The precise obstruction to recovering odd parity from a negative sign. -/
theorem grading_conjugation_neg_iff_even_two_torsion (p x : A) :
    grading p * x * grading p = -x ↔ (2 : ℕ) • evenPart p x = 0 := by
  rw [two_nsmul_evenPart, add_comm x, add_eq_zero_iff_eq_neg]

/-- Positive and negative sign conditions can overlap in the presence of torsion. -/
theorem grading_conjugation_both_signs_iff (p x : A) :
    (grading p * x * grading p = x ∧ grading p * x * grading p = -x) ↔
      ((2 : ℕ) • oddPart p x = 0 ∧ (2 : ℕ) • evenPart p x = 0) := by
  rw [grading_conjugation_fixed_iff_odd_two_torsion,
    grading_conjugation_neg_iff_even_two_torsion]

end InfoGeometry.Algebra.PeirceDeWittChiralSplit
