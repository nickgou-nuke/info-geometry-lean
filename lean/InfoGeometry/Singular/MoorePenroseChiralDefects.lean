/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.SquareZeroMoorePenrose
import InfoGeometry.Core.JordanAssociator

/-!
# Square-zero criterion and normalized chiral associators

The ordered support overlap need not be an idempotent. Its vanishing, however,
characterizes square-zero for an MP pair without any commuting-support
assumption. Under that condition the support difference acts chirally on the
two arrows. It is an involution only on the nonharmonic support, and `a + m`
is the normalized algebraic operator, not automatically a metric Dirac operator.

The existing Jordan product includes a factor of one half. Consequently the
self-associator below is `-(1/2) • a`; the unnormalized product gives `-2 • a`.
No Witt bilinear form or Kantor triple-system structure is inferred here.
-/

namespace InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] {a m : R}

/-- Vanishing ordered support overlap characterizes square-zero, even when the
supports do not commute a priori. -/
theorem support_overlap_eq_zero_iff (h : IsMoorePenroseInverse a m) :
    (a * m) * (m * a) = 0 ↔ a * a = 0 := by
  constructor
  · intro hz
    have hrev : (m * a) * (a * m) = 0 := by
      simpa only [star_mul, h.ab_adj_eq, h.ba_adj_eq, star_zero] using congrArg star hz
    calc
      a * a = (a * m * a) * (a * m * a) := by rw [h.aba_eq_a]
      _ = a * ((m * a) * (a * m)) * a := by simp only [mul_assoc]
      _ = 0 := by rw [hrev, mul_zero, zero_mul]
  · exact h.range_mul_domain_eq_zero

/-- The forward arrow has positive left support chirality. -/
theorem chirality_mul_forward (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (a * m - m * a) * a = a := by
  rw [sub_mul, h.aba_eq_a, mul_assoc, ha, mul_zero, sub_zero]

/-- The same arrow has negative right support chirality. -/
theorem forward_mul_chirality (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    a * (a * m - m * a) = -a := by
  rw [mul_sub, ← mul_assoc, ha, zero_mul, ← mul_assoc, h.aba_eq_a, zero_sub]

/-- The inverse arrow has negative left support chirality. -/
theorem chirality_mul_inverse (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (a * m - m * a) * m = -m := by
  rw [sub_mul, mul_assoc, h.inverse_sq_eq_zero ha, mul_zero, h.bab_eq_b, zero_sub]

/-- The inverse arrow has positive right support chirality. -/
theorem inverse_mul_chirality (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    m * (a * m - m * a) = m := by
  rw [mul_sub, ← mul_assoc, h.bab_eq_b, ← mul_assoc, h.inverse_sq_eq_zero ha,
    zero_mul, sub_zero]

/-- The supported chirality anticommutes with the normalized algebraic Dirac operator. -/
theorem chirality_normalizedDirac_anticommute
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (a * m - m * a) * (a + m) + (a + m) * (a * m - m * a) = 0 := by
  rw [mul_add, add_mul, h.chirality_mul_forward ha, h.chirality_mul_inverse ha,
    h.forward_mul_chirality ha, h.inverse_mul_chirality ha]
  abel

section Real
variable [Algebra ℝ R]
open InfoGeometry.Core.JordanPeirceDecomposition

/-- With the owner's normalized Jordan product the self-associator is half
the negative forward arrow, rather than twice that arrow. -/
theorem squareZero_jordan_self_associator
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    jordanMul (jordanMul a a) m - jordanMul a (jordanMul a m) =
      -(1 / 2 : ℝ) • a := by
  rw [InfoGeometry.Core.JordanAssociator.jordan_associator_eq_expanded_double_commutator,
    h.forward_mul_chirality ha, h.chirality_mul_forward ha]
  module

end Real
end InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
