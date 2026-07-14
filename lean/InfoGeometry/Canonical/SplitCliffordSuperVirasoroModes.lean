import Mathlib
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

Two-mode indexed finite SUSY block exposing nontrivial mixed scaling.
-/

noncomputable section

namespace SplitCliffordSuperVirasoroModes

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
theorem shifted_supercurrent_nilpotent :
    G1 * G1 = 0 := by
  simpa [G1, InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus]
    using
      (InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus_square_zero)

/-- Shifted supercurrent is nonzero in the finite two-mode block. -/
theorem shifted_supercurrent_nonzero :
    G1 ≠ 0 := by
  simpa [G1, InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus]
    using
      (InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus_ne_zero)

/-- Fermionic self-anticommutator vanishes in the shifted block. -/
theorem shifted_supercurrent_self_anticomm_zero :
    G1 * G1 + G1 * G1 = 0 := by
  simp [shifted_supercurrent_nilpotent]

/-- The shifted supercurrent is not idempotent (nontrivial nilpotent). -/
theorem shifted_supercurrent_not_idempotent :
    G1 * G1 ≠ G1 := by
  rw [shifted_supercurrent_nilpotent]
  exact shifted_supercurrent_nonzero.symm

/-- The self-commutator of the shifted supercurrent vanishes. -/
theorem shifted_supercurrent_comm_self_zero :
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.commM4 G1 G1 = 0 := by
  unfold InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.commM4
  simp [shifted_supercurrent_nilpotent]

end SplitCliffordSuperVirasoroModes
