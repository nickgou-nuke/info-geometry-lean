import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.Canonical.SplitCliffordSourceWickBase

/-!
# InfoGeometry.Canonical.SplitCliffordTwoModeCAR

Concrete two-mode CAR verification in `4 × 4` real matrices.

It implements:
* `a₁ = a ⊗ 𝕀`
* `a₂ = P ⊗ a`
* `a₁† = a† ⊗ 𝕀`
* `a₂† = P ⊗ a†`

and proves the cross-mode anticommutators vanish.
-/

namespace InfoGeometry.Canonical.SplitCliffordTwoModeCAR

open Matrix
open InfoGeometry.Canonical.SplitCliffordSourceWickBase
open InfoGeometry.Canonical.SplitCliffordJordanWigner

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ
  Matrix.cons_val_three

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Mode 1 annihilation operator: `a₁ = a ⊗ 𝕀`. -/
def a1 : M4R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Mode 1 creation operator: `a₁† = a† ⊗ 𝕀`. -/
def a1Dag : M4R :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Mode 2 annihilation with Jordan-Wigner twist: `a₂ = P ⊗ a`. -/
def a2 : M4R :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 0, 0]

/-- Mode 2 creation with Jordan-Wigner twist: `a₂† = P ⊗ a†`. -/
def a2Dag : M4R :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, -1, 0]

/-- Cross annihilation anticommutator: `{a₁, a₂} = 0`. -/
theorem cross_annihilate_anticommute :
    a1 * a2 + a2 * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1, a2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Cross mixed anticommutator: `{a₁, a₂†} = 0`. -/
theorem cross_mixed_anticommute :
    a1 * a2Dag + a2Dag * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Each annihilation operator is nilpotent. -/
theorem mode1_square_zero :
    a1 * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1, Matrix.mul_apply, Fin.sum_univ_four]

theorem mode2_square_zero :
    a2 * a2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Each creation operator is nilpotent. -/
theorem mode1Dag_square_zero :
    a1Dag * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1Dag, Matrix.mul_apply, Fin.sum_univ_four]

theorem mode2Dag_square_zero :
    a2Dag * a2Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- The reversed mixed cross anticommutator also vanishes. -/
theorem cross_mixed_anticommute_rev :
    a2Dag * a1 + a1 * a2Dag = 0 := by
  simpa [add_comm] using cross_mixed_anticommute

/-- Creation operators in distinct modes anticommute. -/
theorem cross_creation_anticommute :
    a1Dag * a2Dag + a2Dag * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Local CAR for mode 1: `{a₁, a₁†} = 1`. -/
theorem mode1_car_identity :
    a1 * a1Dag + a1Dag * a1 = (1 : M4R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1, a1Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Local CAR for twisted mode 2: `{a₂, a₂†} = 1`. -/
theorem mode2_car_identity :
    a2 * a2Dag + a2Dag * a2 = (1 : M4R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-! ### Trace-form readouts -/

/-- Explicit trace on `M4R`. -/
def tr4 (A : M4R) : ℝ := A 0 0 + A 1 1 + A 2 2 + A 3 3

/-- Bilinear trace pairing `⟨A,B⟩ = tr4 (A*B)`. -/
def traceForm4 (A B : M4R) : ℝ := tr4 (A * B)

@[simp] theorem tr4_zero : tr4 (0 : M4R) = 0 := by
  simp [tr4]

@[simp] theorem tr4_one : tr4 (1 : M4R) = 4 := by
  norm_num [tr4]

/-- Trace readout of the cross annihilation anticommutator `{a₁,a₂}=0`. -/
theorem traceForm4_cross_annihilate_anticommute :
    tr4 (a1 * a2 + a2 * a1) = 0 := by
  simpa [cross_annihilate_anticommute] using tr4_zero

/-- Trace readout of the cross mixed anticommutator `{a₁,a₂†}=0`. -/
theorem traceForm4_cross_mixed_anticommute :
    tr4 (a1 * a2Dag + a2Dag * a1) = 0 := by
  simpa [cross_mixed_anticommute] using tr4_zero

/-- Trace readout of local CAR for mode 1. -/
theorem traceForm4_mode1_car :
    tr4 (a1 * a1Dag + a1Dag * a1) = 4 := by
  simpa [mode1_car_identity] using tr4_one

/-- Trace readout of local CAR for mode 2. -/
theorem traceForm4_mode2_car :
    tr4 (a2 * a2Dag + a2Dag * a2) = 4 := by
  simpa [mode2_car_identity] using tr4_one

end InfoGeometry.Canonical.SplitCliffordTwoModeCAR
