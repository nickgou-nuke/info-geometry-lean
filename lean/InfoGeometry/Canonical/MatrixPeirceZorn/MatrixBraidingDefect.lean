/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixReflection

/-!
# Exact sum and difference of mixed matrix-valued associators

The symmetric cross-product defect and the antisymmetric cross-product
difference have distinct coefficient formulas. The former consists of matrix
commutators; the latter consists of matrix anticommutators. This distinction
determines the sign in the mixed-associator identities.

The final section retains arbitrary square matrices `A`, `B`, and `C`. The
vector slots locate ordered matrix products without restricting their entries
or assuming that any two matrices commute.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Antisymmetrizing the ordered cross product gives coefficient anticommutators. -/
theorem cross_difference_eq_anticommutators (p q : Vec n) :
    cross p q - cross q p =
      ![(p 1 * q 2 + q 2 * p 1) - (p 2 * q 1 + q 1 * p 2),
        (p 2 * q 0 + q 0 * p 2) - (p 0 * q 2 + q 2 * p 0),
        (p 0 * q 1 + q 1 * p 0) - (p 1 * q 0 + q 0 * p 1)] := by
  funext i
  fin_cases i <;> simp [cross] <;> noncomm_ring

/-- The exact residual of replacing the mixed-associator sum by a negated
symmetric cross defect. -/
theorem mixed_associator_sum_neg_defect_residual (w u v : Vec n) :
    (associator (lower w) (upper u) (upper v) +
      associator (upper u) (upper v) (lower w)) -
        upper (crossDefect w (-(cross u v))) =
          2 • upper (cross w (cross u v)) := by
  rw [mixed_associator_sum]
  simp only [crossDefect, cross_neg, neg_cross, upper_sub, upper_add, upper_neg,
    two_nsmul]
  abel

/-- Over complex matrices the incorrect signed-defect equation holds exactly
when its additional ordered cross term vanishes. -/
theorem mixed_associator_sum_eq_neg_defect_iff (w u v : Vec n) :
    associator (lower w) (upper u) (upper v) +
      associator (upper u) (upper v) (lower w) =
        upper (crossDefect w (-(cross u v))) ↔
          cross w (cross u v) = 0 := by
  rw [← sub_eq_zero, mixed_associator_sum_neg_defect_residual]
  constructor
  · intro h
    funext i j k
    have hi := congrArg (fun X : Carrier n => X.2.1 i j k) h
    simp only [two_nsmul] at hi
    change cross w (cross u v) i j k + cross w (cross u v) i j k = 0 at hi
    exact add_self_eq_zero.mp hi
  · intro h
    simp [h]

theorem mixed_associator_sum_ne_neg_defect (w u v : Vec n)
    (h : cross w (cross u v) ≠ 0) :
    associator (lower w) (upper u) (upper v) +
      associator (upper u) (upper v) (lower w) ≠
        upper (crossDefect w (-(cross u v))) :=
  mt (mixed_associator_sum_eq_neg_defect_iff w u v).mp h

omit [Fintype n] [DecidableEq n] in
theorem upper_single_eq_zero_iff (M : Op n) :
    upper ![M, 0, 0] = 0 ↔ M = 0 := by
  constructor
  · intro h
    simpa [upper] using congrArg (fun X : Carrier n => X.2.1 0) h
  · intro h
    simp [upper, h]

omit [DecidableEq n] in
/-- An ordered triple product of unrestricted matrices occupies one vector slot. -/
theorem nested_cross_matrix_family (A B C : Op n) :
    cross ![0, C, 0] (cross ![A, 0, 0] ![0, B, 0]) =
      ![C * (A * B), 0, 0] := by
  funext i
  fin_cases i <;> simp [cross]

/-- The sum is a matrix anticommutator, with the order of all factors retained. -/
theorem mixed_associator_sum_matrix_family (A B C : Op n) :
    associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) +
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0]) =
        upper ![C * (A * B) + (A * B) * C, 0, 0] := by
  rw [mixed_associator_sum]
  congr 1
  funext i
  fin_cases i <;> simp [cross]

/-- The difference is a matrix commutator, with no commutativity assumption. -/
theorem mixed_associator_difference_matrix_family (A B C : Op n) :
    associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) -
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0]) =
        upper ![opBracket C (A * B), 0, 0] := by
  rw [mixed_associator_difference]
  congr 1
  funext i
  fin_cases i <;> simp [crossDefect, cross, opBracket]
  noncomm_ring

omit [DecidableEq n] in
theorem neg_cross_defect_matrix_family (A B C : Op n) :
    upper (crossDefect ![0, C, 0] (-(cross ![A, 0, 0] ![0, B, 0]))) =
      upper ![-(C * (A * B)) + (A * B) * C, 0, 0] := by
  congr 1
  funext i
  fin_cases i <;> simp [crossDefect, cross]

theorem mixed_associator_residual_matrix_family (A B C : Op n) :
    (associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) +
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0])) -
        upper (crossDefect ![0, C, 0] (-(cross ![A, 0, 0] ![0, B, 0]))) =
          2 • upper ![C * (A * B), 0, 0] := by
  rw [mixed_associator_sum_neg_defect_residual, nested_cross_matrix_family]

theorem mixed_associator_sum_eq_neg_defect_matrix_family_iff (A B C : Op n) :
    associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) +
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0]) =
        upper (crossDefect ![0, C, 0] (-(cross ![A, 0, 0] ![0, B, 0]))) ↔
          C * (A * B) = 0 := by
  rw [mixed_associator_sum_eq_neg_defect_iff, nested_cross_matrix_family]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h
    simp [h]

/-- A nonzero ordered matrix product gives a whole family of failures of the
incorrect signed-defect equation. -/
theorem mixed_associator_sum_ne_neg_defect_matrix_family (A B C : Op n)
    (h : C * (A * B) ≠ 0) :
    associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) +
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0]) ≠
        upper (crossDefect ![0, C, 0] (-(cross ![A, 0, 0] ![0, B, 0]))) :=
  mt (mixed_associator_sum_eq_neg_defect_matrix_family_iff A B C).mp h

/-- The mixed-associator difference detects noncommutation of two matrix operators. -/
theorem mixed_associator_difference_matrix_family_ne_zero_iff (A B C : Op n) :
    associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) -
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0]) ≠ 0 ↔
        ¬ Commute C (A * B) := by
  rw [mixed_associator_difference_matrix_family, ne_eq, upper_single_eq_zero_iff]
  change ¬ (C * (A * B) - (A * B) * C = 0) ↔
    ¬ (C * (A * B) = (A * B) * C)
  rw [sub_eq_zero]

theorem mixed_associator_sum_matrix_family_ne_zero (A B C : Op n)
    (h : C * (A * B) + (A * B) * C ≠ 0) :
    associator (lower ![0, C, 0]) (upper ![A, 0, 0]) (upper ![0, B, 0]) +
      associator (upper ![A, 0, 0]) (upper ![0, B, 0]) (lower ![0, C, 0]) ≠ 0 := by
  rw [mixed_associator_sum_matrix_family, ne_eq, upper_single_eq_zero_iff]
  exact h

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn
