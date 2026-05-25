import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordSourceWickBase

Concrete finite Wick base case in `M₂(ℝ)`.

This file uses the nilpotent matrix atom

`N = [[0,1],[0,0]]`

as annihilation operator, with transpose as creation operator.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceWickBase

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Parabolic nilpotent atom. -/
def N : M2R :=
  !![0, 1;
     0, 0]

/-- Local annihilation operator. -/
def a : M2R := N

/-- Local creation operator. -/
def aDag : M2R :=
  !![0, 0;
     1, 0]

/-- Local vacuum vector `|0⟩ = [1,0]ᵀ`. -/
def vac : Matrix (Fin 2) (Fin 1) ℝ :=
  !![1;
     0]

/-- Vacuum annihilation: `a |0⟩ = 0`. -/
theorem vacuum_annihilation :
    a * vac = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [a, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local CAR identity: `{a, a†} = 1`. -/
theorem local_car_identity :
    a * aDag + aDag * a = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local commutator on vacuum: `[a, a†] |0⟩ = |0⟩`. -/
theorem local_wick_vacuum_commutator :
    (a * aDag - aDag * a) * vac = vac := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [a, aDag, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.SplitCliffordSourceWickBase
