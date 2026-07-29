import InfoGeometry.Clifford.FiniteTiltDiracShell
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.FiniteTiltDiracShellBridge

Thin bridge exports for the finite tilt Dirac shell.
-/

namespace InfoGeometry.Clifford.FiniteTiltDiracShellBridge

open FiniteTiltDiracShell

@[rep_depth operator]
theorem finiteTiltCurrentDensity_eq_boundaryCurrent_bridge :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent := by
  exact finiteTiltCurrentDensity_eq_boundaryCurrent

/-- Combined concrete shell-square and boundary-current theorem. -/
@[rep_depth operator]
theorem FiniteTiltDiracShellBridgeOwnerTarget :
  (
    ∀ m : ℝ,
      finiteTiltDiracShell m * finiteTiltDiracShell m =
        (m ^ 2 : ℝ) • (1 : Mat2)
  ) ∧
  finiteTiltCurrentDensity = finiteTiltBoundaryCurrent :=
  ⟨finiteTiltDiracShell_sq, finiteTiltCurrentDensity_eq_boundaryCurrent_bridge⟩

@[rep_depth operator]
theorem finiteTiltDiracShellBridgeOwnerTarget :
    (∀ m : ℝ,
      finiteTiltDiracShell m * finiteTiltDiracShell m =
        (m ^ 2 : ℝ) • (1 : Mat2)) ∧
      finiteTiltCurrentDensity = finiteTiltBoundaryCurrent :=
  FiniteTiltDiracShellBridgeOwnerTarget

@[rep_depth operator]
theorem finiteTiltDiracShellBridge_shell_square (m : ℝ) :
    finiteTiltDiracShell m * finiteTiltDiracShell m = (m ^ 2 : ℝ) • (1 : Mat2) := by
  exact finiteTiltDiracShell_sq m

@[rep_depth operator]
theorem finiteTiltDiracShellBridge_current_density_eq :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent := by
  exact finiteTiltCurrentDensity_eq_boundaryCurrent

end InfoGeometry.Clifford.FiniteTiltDiracShellBridge
