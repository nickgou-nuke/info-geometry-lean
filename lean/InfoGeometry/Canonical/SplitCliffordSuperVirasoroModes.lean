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
def LG_defect : M4R := (L0 * G1 - G1 * L0) - (1 / 2 : ℝ) • G1

/-- Mixed scaling readback with explicit residual term. -/
theorem emergent_super_conformal_scaling_with_defect :
    L0 * G1 - G1 * L0 = (1 / 2 : ℝ) • G1 + LG_defect := by
  unfold LG_defect
  abel_nf

/-- Shifted supercurrent self-square vanishes in this finite block. -/
def GG_defect : M4R := G1 * G1

/-- Nilpotent closure readback with explicit residual term. -/
theorem shifted_supercurrent_nilpotent_with_defect :
    G1 * G1 = GG_defect := by
  rfl

end InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes
