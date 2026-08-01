import Mathlib.Tactic
import InfoGeometry.Topology.WallpaperSymmetry

/-!
# Finite exceptional-point matrix witness

This module repairs the cognitive-topology exceptional-point surface by
removing vacuous existence claims.  It proves only a concrete finite matrix
fact: the standard `2 x 2` Jordan block has a nonzero square-zero deviation
from its scalar eigenvalue.

#### BUCKET 1: CLOSED FINITE THEOREMS

`jordanNilpotent_square_zero`, `jordanNilpotent_ne_zero`,
`jordanBlock_deviation`, `jordanBlock_deviation_square_zero`, and
`jordanBlock_is_matrixExceptionalPoint`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`pg_relation_keeps_explicit_jordan_witness`.

#### BUCKET 3: OPEN CLOSURE DEBT

The theorem that wallpaper topology forces an exceptional point for an arbitrary
non-Hermitian band/attention family is not proved here.  Neither is any theorem
that real LLM training reaches this finite witness.
-/

noncomputable section

namespace InfoGeometry.CognitiveTopology.ExceptionalPoints

open Matrix InfoGeometry.Topology.Wallpaper

/-- Concrete `2 x 2` complex matrix carrier for the finite EP witness. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The nilpotent part of the standard size-two Jordan block. -/
def jordanNilpotent : Mat2C :=
  ![![0, 1],
    ![0, 0]]

/-- The standard Jordan block with repeated eigenvalue `lam`. -/
def jordanBlock (lam : ℂ) : Mat2C :=
  lam • (1 : Mat2C) + jordanNilpotent

/--
A finite algebraic exceptional point witness: the deviation from a scalar
matrix is nonzero and square-zero.
-/
def IsMatrixExceptionalPoint (A : Mat2C) (lam : ℂ) : Prop :=
  let D := A - lam • (1 : Mat2C)
  D * D = 0 ∧ D ≠ 0

/-- The Jordan nilpotent has square zero. -/
theorem jordanNilpotent_square_zero :
    jordanNilpotent * jordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanNilpotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Jordan nilpotent is not the zero matrix. -/
theorem jordanNilpotent_ne_zero :
    jordanNilpotent ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [jordanNilpotent] at h01

/-- The deviation of a Jordan block from its scalar part is the nilpotent part. -/
theorem jordanBlock_deviation (lam : ℂ) :
    jordanBlock lam - lam • (1 : Mat2C) = jordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanBlock, jordanNilpotent]

/-- The deviation of a Jordan block has square zero. -/
theorem jordanBlock_deviation_square_zero (lam : ℂ) :
    (jordanBlock lam - lam • (1 : Mat2C)) *
        (jordanBlock lam - lam • (1 : Mat2C)) = 0 := by
  rw [jordanBlock_deviation, jordanNilpotent_square_zero]

/-- The standard Jordan block is a finite matrix exceptional-point witness. -/
theorem jordanBlock_is_matrixExceptionalPoint (lam : ℂ) :
    IsMatrixExceptionalPoint (jordanBlock lam) lam := by
  dsimp [IsMatrixExceptionalPoint]
  exact ⟨jordanBlock_deviation_square_zero lam, by
    rw [jordanBlock_deviation]
    exact jordanNilpotent_ne_zero⟩

/--
The wallpaper `pg` relation can be carried alongside the explicit Jordan
witness, but it is not used here to force the witness to exist.
-/
theorem pg_relation_keeps_explicit_jordan_witness (p : Lattice2D) (lam : ℂ)
    (h_pg : G (T_y p) = T_y.symm (G p)) :
    (G (T_y p) = T_y.symm (G p)) ∧ IsMatrixExceptionalPoint (jordanBlock lam) lam := by
  refine ⟨?_, ?_⟩
  · exact h_pg
  · exact jordanBlock_is_matrixExceptionalPoint lam

end InfoGeometry.CognitiveTopology.ExceptionalPoints

end noncomputable section
