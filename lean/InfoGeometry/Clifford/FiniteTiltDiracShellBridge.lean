import Mathlib
import InfoGeometry.Clifford.FiniteTiltDiracShell
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Clifford.FiniteTiltDiracShellBridge

Bridge layer for the finite tilt Dirac shell.

This file does not add a new operator model. It only reexports the finite
shell closure and boundary-current theorems proved in
`FiniteTiltDiracShell`.

No OSp representation theorem.
No current-density socket.
No zeta claim.
-/

noncomputable section

namespace InfoGeometry.Clifford.FiniteTiltDiracShellBridge

open InfoGeometry.Clifford.FiniteTiltDiracShell

/-- Bridge reexport of the finite shell closure theorem. -/
@[bridge_target_tag]
theorem finiteTiltDiracShell_sq_bridge (m : ℝ) :
    finiteTiltDiracShell m * finiteTiltDiracShell m =
      (m ^ 2 : ℝ) • (1 : Mat2) :=
  finiteTiltDiracShell_sq m

/-- Bridge reexport of the finite boundary-current nilpotence theorem. -/
@[bridge_target_tag]
theorem finiteTiltBoundaryCurrent_sq_zero_bridge :
    finiteTiltBoundaryCurrent * finiteTiltBoundaryCurrent = 0 :=
  finiteTiltBoundaryCurrent_sq_zero

/-- Bridge reexport of the shell decomposition theorem. -/
@[bridge_target_tag]
theorem finiteTiltDiracShell_eq_boundaryCurrent_add_mass_bridge (m : ℝ) :
    finiteTiltDiracShell m = finiteTiltBoundaryCurrent + m • tiltEvenJ :=
  finiteTiltDiracShell_eq_boundaryCurrent_add_mass m

/-- Owner target for the finite tilt shell bridge. -/
@[owner_target_tag]
def FiniteTiltDiracShellBridgeOwnerTarget : Prop :=
  ∀ m : ℝ,
    finiteTiltDiracShell m * finiteTiltDiracShell m =
      (m ^ 2 : ℝ) • (1 : Mat2) ∧
    finiteTiltBoundaryCurrent * finiteTiltBoundaryCurrent = 0 ∧
    finiteTiltDiracShell m = finiteTiltBoundaryCurrent + m • tiltEvenJ

/-- The finite tilt shell bridge owner target is closed. -/
theorem finiteTiltDiracShellBridgeOwnerTarget :
    FiniteTiltDiracShellBridgeOwnerTarget := by
  intro m
  exact ⟨finiteTiltDiracShell_sq m, finiteTiltBoundaryCurrent_sq_zero,
    finiteTiltDiracShell_eq_boundaryCurrent_add_mass m⟩

end InfoGeometry.Clifford.FiniteTiltDiracShellBridge
