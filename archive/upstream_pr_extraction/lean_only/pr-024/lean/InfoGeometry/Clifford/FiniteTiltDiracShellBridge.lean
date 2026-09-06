import InfoGeometry.Clifford.FiniteTiltDiracShell
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.FiniteTiltDiracShellBridge

Thin bridge exports for the finite tilt Dirac shell.
-/

namespace InfoGeometry.Clifford.FiniteTiltDiracShellBridge

open InfoGeometry.Clifford.FiniteTiltDiracShell

@[rep_depth operator]
theorem finiteTiltCurrentDensity_eq_boundaryCurrent_bridge :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent := by
  exact finiteTiltCurrentDensity_eq_boundaryCurrent

@[rep_depth operator]
structure FiniteTiltDiracShellBridgeOwnerTarget where
  shell_square :
    ∀ m : ℝ,
      finiteTiltDiracShell m * finiteTiltDiracShell m =
        (m ^ 2 : ℝ) • (1 : Mat2)
  current_density_eq :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent

@[rep_depth operator]
theorem finiteTiltDiracShellBridgeOwnerTarget :
    FiniteTiltDiracShellBridgeOwnerTarget := by
  exact
    { shell_square := finiteTiltDiracShellOwnerTarget_shell_square
      current_density_eq := finiteTiltCurrentDensity_eq_boundaryCurrent_bridge }

@[rep_depth operator]
theorem finiteTiltDiracShellBridge_shell_square (m : ℝ) :
    finiteTiltDiracShell m * finiteTiltDiracShell m =
      (m ^ 2 : ℝ) • (1 : Mat2) :=
  let pkt := finiteTiltDiracShellBridgeOwnerTarget
  pkt.shell_square m

@[rep_depth operator]
theorem finiteTiltDiracShellBridge_current_density_eq :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent :=
  let pkt := finiteTiltDiracShellBridgeOwnerTarget
  pkt.current_density_eq

end InfoGeometry.Clifford.FiniteTiltDiracShellBridge
