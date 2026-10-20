/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-!
# QCCR commutator–anticommutator closure

The inhomogeneous Kronecker correction is retained explicitly in the native
q-CCR operator owner.
-/

import InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

namespace InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzClosure

open InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

variable {ι R Op : Type*} [DecidableEq ι] [CommRing R] [Ring Op]
  [StarRing Op] [Algebra R Op]

/-- The homogeneous part of the q-CCR relation, with the diagonal correction explicit. -/
def commutator (X Y : Op) : Op := X * Y - Y * X

def anticommutator (X Y : Op) : Op := X * Y + Y * X

/-- The q-CCR relation determines the commutator, including its diagonal correction. -/
theorem qccr_commutator (A : QCCROperators ι R Op) (i j : ι) :
    commutator (star (A.a i)) (A.a j) =
      (if i = j then (1 : Op) else 0) + (A.q - 1) • (A.a j * star (A.a i)) := by
  unfold commutator
  rw [A.q_commutation]
  module

/-- The q-CCR relation determines the anticommutator, including its diagonal correction. -/
theorem qccr_anticommutator (A : QCCROperators ι R Op) (i j : ι) :
    anticommutator (star (A.a i)) (A.a j) =
      (if i = j then (1 : Op) else 0) + (A.q + 1) • (A.a j * star (A.a i)) := by
  unfold anticommutator
  rw [A.q_commutation]
  module

/-- Exact commutator--anticommutator closure for q-CCR, with the diagonal Kronecker correction. -/
theorem qccr_comm_anti_closure (A : QCCROperators ι R Op) (i j : ι) :
    (A.q + 1) • commutator (star (A.a i)) (A.a j) =
      (A.q - 1) • anticommutator (star (A.a i)) (A.a j) +
        2 • (if i = j then (1 : Op) else 0) := by
  rw [qccr_commutator, qccr_anticommutator]
  module

/-- The off-diagonal closure has no Kronecker correction. -/
theorem qccr_offDiagonal_comm_anti_closure
    (A : QCCROperators ι R Op) (i j : ι) (hij : i ≠ j) :
    (A.q + 1) • commutator (star (A.a i)) (A.a j) =
      (A.q - 1) • anticommutator (star (A.a i)) (A.a j) := by
  rw [qccr_comm_anti_closure]
  simp [hij]

end InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzClosure
