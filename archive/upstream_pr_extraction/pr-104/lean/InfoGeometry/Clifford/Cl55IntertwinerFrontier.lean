import Mathlib.Data.Matrix.Basic

/-! Typed frontier for a possible KZ/Cl(5,5) comparison.

The file proves only the algebraic equivalence between conjugation and
intertwining equations once a two-sided inverse is supplied.  It does not
construct a monodromy operator or an intertwiner.
-/

namespace InfoGeometry.Clifford.Cl55IntertwinerFrontier

structure Datum (R : Type*) (ι : Type*) [Semiring R] [Fintype ι]
    [DecidableEq ι] where
  monodromy : Matrix ι ι R
  rotor : Matrix ι ι R
  intertwiner : Matrix ι ι R
  inverse : Matrix ι ι R
  inverse_left : inverse * intertwiner = 1
  inverse_right : intertwiner * inverse = 1

theorem conjugation_iff_intertwining {R : Type*} [Semiring R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : Datum R ι) :
    d.intertwiner * d.monodromy * d.inverse = d.rotor ↔
      d.intertwiner * d.monodromy = d.rotor * d.intertwiner := by
  constructor
  · intro h
    calc
      d.intertwiner * d.monodromy =
          (d.intertwiner * d.monodromy * d.inverse) * d.intertwiner := by
            rw [mul_assoc, d.inverse_left, mul_one]
      _ = d.rotor * d.intertwiner := by rw [h]
  · intro h
    calc
      d.intertwiner * d.monodromy * d.inverse =
          (d.rotor * d.intertwiner) * d.inverse := by rw [← h]
      _ = d.rotor := by rw [mul_assoc, d.inverse_right, mul_one]

end InfoGeometry.Clifford.Cl55IntertwinerFrontier
