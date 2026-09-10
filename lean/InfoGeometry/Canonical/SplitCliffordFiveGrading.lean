import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.SplitCliffordFiveGrading

Concrete five-grading style operators on the two-mode Jordan-Wigner `4 × 4`
matrix model, with direct commutator evaluations.
-/

namespace InfoGeometry.Canonical.SplitCliffordFiveGrading

open Matrix
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

abbrev M4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- Level `0` core (diagonal Cartan-like operator). -/
def g0Core : M4R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Level `+1` boundary (creation sector). -/
def gPlus1 : M4R := SplitCliffordTwoModeCAR.a1Dag + SplitCliffordTwoModeCAR.a2Dag

/-- Level `-1` boundary (annihilation sector). -/
def gMinus1 : M4R := SplitCliffordTwoModeCAR.a1 + SplitCliffordTwoModeCAR.a2

/-- Commutator in `M4R`. -/
def comm4 (X Y : M4R) : M4R := X * Y - Y * X

/--
Direct boundary commutator evaluation.
-/
theorem grading_boundary_commutator_explicit :
    comm4 gPlus1 gMinus1 =
      !![-2, 0, 0, 0;
          0, 0, 2, 0;
          0, 2, 0, 0;
          0, 0, 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm4, gPlus1, gMinus1,
      SplitCliffordTwoModeCAR.a1, SplitCliffordTwoModeCAR.a1Dag,
      SplitCliffordTwoModeCAR.a2, SplitCliffordTwoModeCAR.a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

end InfoGeometry.Canonical.SplitCliffordFiveGrading
