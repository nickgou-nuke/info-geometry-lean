import Mathlib
import InfoGeometryCore.Basic

/-!
# InfoGeometry.Canonical.SplitCliffordSourceWickBase

Concrete finite Wick base case in `M₂(ℝ)`.

This file uses the nilpotent matrix atom

`N = [[0,1],[0,0]]`

as annihilation operator, with transpose as creation operator.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceWickBase

open Matrix

open InfoGeometryCore

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
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local CAR identity: `{a, a†} = 1`. -/
theorem local_car_identity :
    a * aDag + aDag * a = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local commutator on vacuum: `[a, a†] |0⟩ = |0⟩`. -/
theorem local_wick_vacuum_commutator :
    (a * aDag - aDag * a) * vac = vac := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, aDag, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Local Jordan--Wigner parity from the Wick atom -/

/--
The local fermion parity operator is

  P = a a† - a† a.

In this concrete `M₂(ℝ)` model it is the diagonal grading operator.
-/
def parity : M2R :=
  a * aDag - aDag * a

/--
The local parity operator is an involution:

  P² = 1.
-/
theorem parity_sq_eq_one :
    parity * parity = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [parity, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity anticommutes with annihilation:

  P a + a P = 0.
-/
theorem parity_anticommutes_annihilation :
    parity * a + a * parity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [parity, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
Parity anticommutes with creation:

  P a† + a† P = 0.
-/
theorem parity_anticommutes_creation :
    parity * aDag + aDag * parity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [parity, a, aDag, N, Matrix.mul_apply, Fin.sum_univ_two]

/--
The local Jordan--Wigner grading profile.

This is the finite algebraic fact needed before any two-mode or multi-mode
fermionic construction.
-/
theorem local_jordan_wigner_parity_profile :
    parity * parity = (1 : M2R) ∧
    parity * a + a * parity = 0 ∧
    parity * aDag + aDag * parity = 0 := by
  exact
    ⟨parity_sq_eq_one,
     parity_anticommutes_annihilation,
     parity_anticommutes_creation⟩

end InfoGeometry.Canonical.SplitCliffordSourceWickBase
