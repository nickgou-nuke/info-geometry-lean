import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

section Pseudoinverses

variable {R : Type*} [Ring R] [StarRing R]

structure IsMoorePenrose (A A_plus : R) : Prop where
  aba : A * A_plus * A = A
  bab : A_plus * A * A_plus = A_plus
  sa  : star (A * A_plus) = A * A_plus
  as  : star (A_plus * A) = A_plus * A

structure IsDrazinIndexOne (A A_D : R) : Prop where
  comm : A * A_D = A_D * A
  bab  : A_D * A * A_D = A_D
  aab  : A * A * A_D = A

def defect_ghost (A_plus A_D : R) : R := A_plus - A_D

omit [StarRing R] in
theorem zero_ghost_implies_metric_commutation
    (A A_plus A_D : R)
    (h_drazin : IsDrazinIndexOne A A_D)
    (h_ghost : defect_ghost A_plus A_D = 0) :
    A * A_plus = A_plus * A := by
  have h_eq : A_plus = A_D := sub_eq_zero.mp h_ghost
  rw [h_eq]
  exact h_drazin.comm

omit [StarRing R] in
theorem operator_ghost_commutator
    (A A_plus A_D : R)
    (h_drazin : IsDrazinIndexOne A A_D) :
    A * (defect_ghost A_plus A_D) - (defect_ghost A_plus A_D) * A =
    A * A_plus - A_plus * A := by
  dsimp [defect_ghost]
  have h_comm : A * A_D = A_D * A := h_drazin.comm
  calc
    A * (A_plus - A_D) - (A_plus - A_D) * A
      = A * A_plus - A * A_D - (A_plus * A - A_D * A) := by simp only [mul_sub, sub_mul]
    _ = A * A_plus - A_plus * A - A * A_D + A_D * A := by abel
    _ = A * A_plus - A_plus * A - A * A_D + A * A_D := by rw [h_comm]
    _ = A * A_plus - A_plus * A := by abel

end Pseudoinverses

end InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge
