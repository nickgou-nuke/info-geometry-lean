/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

namespace Omega.EA

/-- Number of binary operation tables on the fixed carrier `Fin n`. -/
def stable_audit_small_order_obstruction_operation_table_count (n : ℕ) : ℕ :=
  n ^ (n * n)

/-- The function space of binary operations on `Fin n` has exactly `n^(n*n)` elements.
This counts all binary operations, without imposing associativity or other laws. -/
theorem stable_audit_small_order_obstruction_operation_table_count_eq_card (n : ℕ) :
    Fintype.card (Fin n → Fin n → Fin n) =
      stable_audit_small_order_obstruction_operation_table_count n := by
  simp [stable_audit_small_order_obstruction_operation_table_count,
    pow_mul]

/-- There are sixteen binary operation tables on a two-element carrier. -/
theorem stable_audit_small_order_obstruction_order2_table_count :
    Fintype.card (Fin 2 → Fin 2 → Fin 2) = 16 := by
  rw [stable_audit_small_order_obstruction_operation_table_count_eq_card]
  norm_num [stable_audit_small_order_obstruction_operation_table_count]

/-- There are 19,683 binary operation tables on a three-element carrier. -/
theorem stable_audit_small_order_obstruction_order3_table_count :
    Fintype.card (Fin 3 → Fin 3 → Fin 3) = 19683 := by
  rw [stable_audit_small_order_obstruction_operation_table_count_eq_card]
  norm_num [stable_audit_small_order_obstruction_operation_table_count]

end Omega.EA
