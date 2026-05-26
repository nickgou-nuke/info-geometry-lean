import Mathlib
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

/-!
# InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

Two-mode indexed finite SUSY block exposing nontrivial mixed scaling.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

open Matrix
open InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Stress zero-mode block. -/
def L0 : M4R :=
  !![(1 / 2 : ℝ), 0, 0, 0;
     0, (1 / 2 : ℝ), 0, 0;
     0, 0, -(1 / 2 : ℝ), 0;
     0, 0, 0, -(1 / 2 : ℝ)]

/-- Shifted supercurrent mode block. -/
def G1 : M4R := a1Dag * a2

/-- Emergent mixed scaling in the shifted two-mode block. -/
theorem emergent_super_conformal_scaling :
    L0 * G1 - G1 * L0 = (1 / 2 : ℝ) • G1 := by
  dsimp [L0, G1, a1Dag, a2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four]

/-- Shifted supercurrent self-square vanishes in this finite block. -/
theorem shifted_supercurrent_nilpotent :
    G1 * G1 = 0 := by
  dsimp [G1, a1Dag, a2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four]

end InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

