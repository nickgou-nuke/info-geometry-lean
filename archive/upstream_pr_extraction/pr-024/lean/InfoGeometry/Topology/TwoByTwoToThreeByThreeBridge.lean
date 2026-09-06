import Mathlib
import InfoGeometry.CognitiveTopology.ExceptionalPoints
import InfoGeometry.Topology.AharonovBohmVortices

/-!
# Finite `2 × 2` to `3 × 3` block bridge

This module reconciles the finite `2 × 2` exceptional-point Jordan witness with
the finite `3 × 3` projective/vortex carrier.

There are two maps, kept deliberately separate:

* `linearEmbed2to3 A = diag(A, 0)`, which preserves nilpotent square-zero data;
* `projectiveEmbed2to3 A = diag(A, 1)`, which is the affine/projective block
  carrier.

The file proves only finite matrix identities.  It does not prove an `SU(2)` to
`SU(3)` unification theorem, Lorentz symmetry breaking, or a physical
parafermion/confinement statement.
-/

namespace InfoGeometry.Topology.TwoByTwoToThreeByThreeBridge

open Matrix
open InfoGeometry.CognitiveTopology.ExceptionalPoints
open InfoGeometry.Topology.Parafermion

/-- Concrete `3 × 3` complex matrix carrier. -/
abbrev Mat3C := Matrix (Fin 3) (Fin 3) ℂ

/-- Linear block inclusion `A ↦ diag(A,0)`, preserving square-zero nilpotents. -/
def linearEmbed2to3 (A : Mat2C) : Mat3C :=
  ![![A 0 0, A 0 1, 0],
    ![A 1 0, A 1 1, 0],
    ![0,     0,     0]]

/-- Projective/affine block inclusion `A ↦ diag(A,1)`. -/
def projectiveEmbed2to3 (A : Mat2C) : Mat3C :=
  ![![A 0 0, A 0 1, 0],
    ![A 1 0, A 1 1, 0],
    ![0,     0,     1]]

/-- The embedded `2 × 2` Jordan nilpotent in the `3 × 3` carrier. -/
def embeddedJordanNilpotent : Mat3C :=
  linearEmbed2to3 jordanNilpotent

/-- The embedded Jordan nilpotent remains square-zero. -/
theorem embeddedJordanNilpotent_square_zero :
    embeddedJordanNilpotent * embeddedJordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embeddedJordanNilpotent, linearEmbed2to3, jordanNilpotent,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- The embedded Jordan nilpotent remains nonzero. -/
theorem embeddedJordanNilpotent_ne_zero :
    embeddedJordanNilpotent ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 3)) (1 : Fin 3)
  norm_num [embeddedJordanNilpotent, linearEmbed2to3, jordanNilpotent] at h01

/-- The scalar/projective reference block for an embedded Jordan block. -/
def scalarExtendedBlock (lam : ℂ) : Mat3C :=
  ![![lam, 0,   0],
    ![0,   lam, 0],
    ![0,   0,   1]]

/-- The projective embedded Jordan block decomposes as scalar block plus nilpotent. -/
theorem projectiveEmbed_jordanBlock_deviation (lam : ℂ) :
    projectiveEmbed2to3 (jordanBlock lam) - scalarExtendedBlock lam =
      embeddedJordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveEmbed2to3, jordanBlock, scalarExtendedBlock,
      embeddedJordanNilpotent, linearEmbed2to3, jordanNilpotent]

/-- The embedded exceptional-point deviation is a finite `3 × 3` square-zero witness. -/
theorem projectiveEmbed_jordanBlock_deviation_square_zero (lam : ℂ) :
    (projectiveEmbed2to3 (jordanBlock lam) - scalarExtendedBlock lam) *
      (projectiveEmbed2to3 (jordanBlock lam) - scalarExtendedBlock lam) = 0 := by
  rw [projectiveEmbed_jordanBlock_deviation, embeddedJordanNilpotent_square_zero]

/-- The embedded exceptional-point deviation is still nonzero. -/
theorem projectiveEmbed_jordanBlock_deviation_ne_zero (lam : ℂ) :
    projectiveEmbed2to3 (jordanBlock lam) - scalarExtendedBlock lam ≠ 0 := by
  rw [projectiveEmbed_jordanBlock_deviation]
  exact embeddedJordanNilpotent_ne_zero

/--
The embedded `2 × 2` nilpotent commutes with the finite third-root vortex
operator.  This is a finite block-diagonal compatibility statement only.
-/
theorem embeddedJordanNilpotent_commutes_vortexOperator (v : AharonovBohmVortex) :
    embeddedJordanNilpotent * vortexOperator v = vortexOperator v * embeddedJordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embeddedJordanNilpotent, linearEmbed2to3, jordanNilpotent,
      vortexOperator, diagonalVortexOperator, Matrix.mul_apply, Fin.sum_univ_three]

end InfoGeometry.Topology.TwoByTwoToThreeByThreeBridge
