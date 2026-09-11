import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Gohberg--Krein / spectral winding anchor

This file gives a deliberately finite, combinatorial anchor for the
non-Hermitian exceptional-point picture.  It does **not** prove the analytic
Gohberg--Krein index theorem.  Instead it proves the exact integer winding of a
four-point finite determinant loop around a single exceptional point, plus the
orientation reversal and Klein doubled-sheet cancellation identities.
-/

namespace GohbergKreinIndex

/-- Four phase sectors for a determinant loop around an exceptional point. -/
inductive Phase4 where
  | east
  | north
  | west
  | south
  deriving DecidableEq, Repr

open Phase4

/-- Integer lattice vertex representing a determinant phase sector. -/
def latticeVertex : Phase4 → ℤ × ℤ
  | east => (1, 0)
  | north => (0, 1)
  | west => (-1, 0)
  | south => (0, -1)

/-- Every lattice vertex is away from the exceptional determinant zero. -/
theorem latticeVertex_nonzero (p : Phase4) : latticeVertex p ≠ (0, 0) := by
  cases p <;> simp [latticeVertex]

/-- Counterclockwise successor on the four phase sectors. -/
def ccw : Phase4 → Phase4
  | east => north
  | north => west
  | west => south
  | south => east

/-- Clockwise successor on the four phase sectors. -/
def cw : Phase4 → Phase4
  | east => south
  | south => west
  | west => north
  | north => east

/-- A quarter-turn contributes one unit of lifted phase in quarter-turn units. -/
def quarterIncrement (_from to_ : Phase4) : ℤ :=
  if to_ = ccw _from then 1 else if to_ = cw _from then -1 else 0

/-- The counterclockwise closed lattice loop around one EP. -/
def ccwLoop : List Phase4 := [east, north, west, south, east]

/-- The clockwise closed lattice loop around one EP. -/
def cwLoop : List Phase4 := [east, south, west, north, east]

/-- Sum lifted phase increments along a finite determinant lattice path. -/
def liftedQuarterSum : List Phase4 → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => quarterIncrement a b + liftedQuarterSum (b :: rest)

/-- Integer winding: four quarter-turns make one full turn. -/
def finiteGKIndex (path : List Phase4) : ℤ := liftedQuarterSum path / 4

/-- The CCW determinant loop has total lifted phase four quarter-turns. -/
theorem ccw_liftedQuarterSum : liftedQuarterSum ccwLoop = 4 := by
  norm_num [ccwLoop, liftedQuarterSum, quarterIncrement, ccw, cw]

/-- The clockwise determinant loop has total lifted phase minus four quarter-turns. -/
theorem cw_liftedQuarterSum : liftedQuarterSum cwLoop = -4 := by
  simp [cwLoop, liftedQuarterSum, quarterIncrement, ccw, cw]

/-- Finite Gohberg--Krein anchor: one positive winding around a single EP. -/
theorem finiteGKIndex_ccwLoop : finiteGKIndex ccwLoop = 1 := by
  norm_num [finiteGKIndex, ccwLoop, liftedQuarterSum, quarterIncrement, ccw, cw]

/-- Orientation reversal gives the negative index. -/
theorem finiteGKIndex_cwLoop : finiteGKIndex cwLoop = -1 := by
  simp [finiteGKIndex, cwLoop, liftedQuarterSum, quarterIncrement, ccw, cw]

/-- A Klein-doubled pair of oppositely oriented sheets has zero net index. -/
theorem klein_doubled_sheet_index_cancels :
    finiteGKIndex ccwLoop + finiteGKIndex cwLoop = 0 := by
  simp [finiteGKIndex, ccwLoop, cwLoop, liftedQuarterSum, quarterIncrement, ccw, cw]


end GohbergKreinIndex
