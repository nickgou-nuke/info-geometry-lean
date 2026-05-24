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
def FiniteTiltDiracShellBridgeOwnerTarget : Prop :=
  ∀ m : ℝ,
    finiteTiltDiracShell m * finiteTiltDiracShell m =
      (m ^ 2 : ℝ) • (1 : Mat2) ∧
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent

@[rep_depth operator]
theorem finiteTiltDiracShellBridgeOwnerTarget :
    FiniteTiltDiracShellBridgeOwnerTarget := by
  intro m
  constructor
  · exact finiteTiltDiracShellOwnerTarget m
  · exact finiteTiltCurrentDensity_eq_boundaryCurrent_bridge

end InfoGeometry.Clifford.FiniteTiltDiracShellBridge
