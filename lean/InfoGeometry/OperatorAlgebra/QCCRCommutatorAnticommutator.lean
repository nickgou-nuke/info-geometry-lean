/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

namespace InfoGeometry.OperatorAlgebra.QCCRCommutatorAnticommutator

variable {R Op : Type*} [Ring R] [Ring Op] [Module R Op]

def QCommutes (q : R) (X Y : Op) : Prop :=
  X * Y = q • (Y * X)

def comm (X Y : Op) : Op := X * Y - Y * X

def anti (X Y : Op) : Op := X * Y + Y * X

omit [Ring R] [Module R Op] in
/-- Operator-valued `Q`-commutation relation `X * Y = Q * (Y * X)` in any associative ring `Op`. -/
def OpQCommutes (Q X Y : Op) : Prop :=
  X * Y = Q * (Y * X)

omit [Ring R] [Module R Op] in
/-- Over any non-commutative ring `Op`, an operator-valued `Q`-commutation relation
`X * Y = Q * (Y * X)` satisfies `(1 + Q) * [X, Y] = (Q - 1) * {X, Y}` without requiring
`Q` to commute with `X` or `Y`. -/
theorem op_comm_anti_relation (Q X Y : Op) (h : OpQCommutes Q X Y) :
    (1 + Q) * comm X Y = (Q - 1) * anti X Y := by
  unfold comm anti OpQCommutes at *
  rw [h]
  noncomm_ring

theorem comm_eq (q : R) (X Y : Op) (h : QCommutes q X Y) :
    comm X Y = q • (Y * X) - Y * X := by
  unfold comm QCommutes at *
  rw [h]

theorem anti_eq (q : R) (X Y : Op) (h : QCommutes q X Y) :
    anti X Y = q • (Y * X) + Y * X := by
  unfold anti QCommutes at *
  rw [h]

theorem comm_anti_relation (q : R) (X Y : Op) (h : QCommutes q X Y) :
    (1 + q) • comm X Y = (q - 1) • anti X Y := by
  rw [comm_eq q X Y h, anti_eq q X Y h]
  rw [add_smul, one_smul, sub_smul, one_smul, smul_sub, smul_add]
  abel

end InfoGeometry.OperatorAlgebra.QCCRCommutatorAnticommutator

namespace InfoGeometry.OperatorAlgebra.QCCRCommutatorAnticommutator
open InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

variable {ι R Op : Type*} [DecidableEq ι] [Ring R] [Ring Op]
  [StarRing Op] [Module R Op]

/-- Off-diagonal QCCR modes satisfy the homogeneous commutator/anticommutator
identity; the inhomogeneous Kronecker term vanishes when the indices differ. -/
theorem qccr_offDiagonal_comm_anti_relation
    (A : QCCROperators ι R Op) (i j : ι) (hij : i ≠ j) :
    (1 + A.q) • (star (A.a i) * A.a j - A.a j * star (A.a i)) =
      (A.q - 1) • (star (A.a i) * A.a j + A.a j * star (A.a i)) := by
  apply comm_anti_relation
  unfold QCommutes
  rw [A.q_commutation i j]
  simp [hij]

end InfoGeometry.OperatorAlgebra.QCCRCommutatorAnticommutator
