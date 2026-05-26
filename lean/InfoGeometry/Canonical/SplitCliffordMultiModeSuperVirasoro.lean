import Mathlib
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordMultiModeSuperVirasoro

Finite multi-mode SUSY seed using explicit two-mode current blocks.
-/

namespace InfoGeometry.Canonical.SplitCliffordMultiModeSuperVirasoro

open Matrix
open InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Computable stress seed (diagonal mode operator). -/
def L0 : M4R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Shifted supercurrent seed from the two-mode current table. -/
def G1 : M4R := Jplus

/-- Multi-mode scaling commutator seed. -/
theorem emergent_super_conformal_scaling :
    L0 * G1 - G1 * L0 = (2 : ℝ) • G1 := by
  dsimp [L0, G1, Jplus, a1Dag, a2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four]

/-- Shifted mode square vanishes in this finite block. -/
theorem shifted_supercurrent_nilpotent :
    G1 * G1 = 0 := by
  simpa [G1] using Jplus_square_zero

end InfoGeometry.Canonical.SplitCliffordMultiModeSuperVirasoro

