import InfoGeometry.OperatorAlgebra.QCCRCore
import Mathlib

noncomputable section

namespace QCCRSupergrading

open InfoGeometry.OperatorAlgebra.QCCRCore

/-!
# q-CCR supergrading shadow

The q-CCR supergrading shadow connects the continuous q-dial to the
Z2-graded superalgebra structure.
-/

/--
The Z2-graded supercommutator evaluated with the q-CCR algebra.

At q = -1 this is the standard fermionic anticommutator.
At q = +1 this is the standard bosonic commutator.
For |q| < 1 this interpolates continuously between them.
-/
def qSuperbracket {Op : Type*} [Ring Op] [Algebra ℝ Op] (q : ℝ) (X Y : Op) : Op :=
  X * Y - q • (Y * X)

/-- The q-superbracket equals the q-CCR relation when applied to the generators. -/
theorem qSuperbracket_matches_qccr {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op] [Algebra ℝ Op]
    (A : QCCRAlgebra N Op) (i j : Fin N) :
  qSuperbracket A.q (star (A.a i)) (A.a j) = if i = j then (1 : Op) else 0 := by
  dsimp [qSuperbracket]
  rw [A.q_commutation i j]
  simp

end QCCRSupergrading
