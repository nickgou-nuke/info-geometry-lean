import InfoGeometry.OperatorAlgebra.QCCRCore
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.QCCRSupergrading

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

theorem qSuperbracket_neg_one_is_anticommutator {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (X Y : Op) :
    qSuperbracket (-1 : ℝ) X Y = X * Y + Y * X := by
  rw [qSuperbracket]
  simp

theorem qSuperbracket_pos_one_is_commutator {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (X Y : Op) :
    qSuperbracket (1 : ℝ) X Y = X * Y - Y * X := by
  rw [qSuperbracket]
  simp

theorem qSuperbracket_zero_is_clean_product {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (X Y : Op) :
    qSuperbracket (0 : ℝ) X Y = X * Y := by
  rw [qSuperbracket]
  simp

theorem q_dial_interpolation_formula {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (X Y : Op) (q : ℝ) :
    qSuperbracket q X Y =
      ((1 - q) / 2) • (X * Y + Y * X) +
        ((1 + q) / 2) • (X * Y - Y * X) := by
  rw [qSuperbracket]
  module

theorem q_superbracket_dial_boundaries {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (X Y : Op) :
    qSuperbracket (0 : ℝ) X Y = X * Y ∧
      qSuperbracket (-1 : ℝ) X Y = X * Y + Y * X ∧
      qSuperbracket (1 : ℝ) X Y = X * Y - Y * X := by
  exact ⟨qSuperbracket_zero_is_clean_product X Y,
    qSuperbracket_neg_one_is_anticommutator X Y,
    qSuperbracket_pos_one_is_commutator X Y⟩

theorem q_neg_one_supertrace_vanishes {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op]
    [Algebra ℝ Op] (A : QCCRAlgebra N Op) (hqneg1 : A.q = -1) (i : Fin N) :
    star (A.a i) * A.a i - A.a i * star (A.a i) =
      (if i = i then (1 : Op) else 0) - 2 • (A.a i * star (A.a i)) := by
  rw [A.q_commutation i i, hqneg1]
  simp [two_smul]
  abel

theorem q_deviation_from_chiral_balance {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op]
    [Algebra ℝ Op] (A : QCCRAlgebra N Op) (i : Fin N) :
    star (A.a i) * A.a i + A.a i * star (A.a i) =
      (if i = i then (1 : Op) else 0) + (A.q + 1) • (A.a i * star (A.a i)) := by
  rw [A.q_commutation i i]
  simp
  module

theorem q_neg_one_chiral_balance_restored {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op]
    [Algebra ℝ Op] (A : QCCRAlgebra N Op) (hqneg1 : A.q = -1) (i : Fin N) :
    star (A.a i) * A.a i + A.a i * star (A.a i) = (1 : Op) := by
  rw [q_deviation_from_chiral_balance A i, hqneg1]
  simp

end InfoGeometry.OperatorAlgebra.QCCRSupergrading
