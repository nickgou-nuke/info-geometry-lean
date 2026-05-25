import Mathlib
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

end InfoGeometry.Canonical.SplitCliffordTwoModeCAR
