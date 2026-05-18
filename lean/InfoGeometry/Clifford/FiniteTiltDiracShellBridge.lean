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

/-- Bridge reexport of the current-density readout theorem. -/
@[bridge_target_tag]
theorem finiteTiltCurrentDensity_eq_boundaryCurrent_bridge :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent :=
  finiteTiltCurrentDensity_eq_boundaryCurrent

/-- Bridge reexport of the shell decomposition theorem. -/
@[bridge_target_tag]
theorem finiteTiltDiracShell_eq_boundaryCurrent_add_mass_bridge (m : ℝ) :
    finiteTiltDiracShell m = finiteTiltBoundaryCurrent + m • tiltEvenJ :=
  finiteTiltDiracShell_eq_boundaryCurrent_add_mass m

/-- Bridge reexport of the shell spectral readout. -/
@[bridge_target_tag]
theorem finiteTiltDiracShellSpectralTarget_bridge :
    FiniteTiltDiracShellSpectralTarget := by
  intro m
  exact finiteTiltDiracShellSpectralTarget m

/-- Owner target for the finite tilt shell bridge. -/
@[owner_target_tag]
def FiniteTiltDiracShellBridgeOwnerTarget : Prop :=
  finiteTiltCurrentDensity = finiteTiltBoundaryCurrent ∧
  ∀ m : ℝ,
    finiteTiltDiracShell m * finiteTiltDiracShell m =
      (m ^ 2 : ℝ) • (1 : Mat2) ∧
    finiteTiltBoundaryCurrent * finiteTiltBoundaryCurrent = 0 ∧
    finiteTiltDiracShell m = finiteTiltBoundaryCurrent + m • tiltEvenJ ∧
    Matrix.trace (finiteTiltDiracShell m) = 0 ∧
    Matrix.det (finiteTiltDiracShell m) = - m ^ 2 ∧
    (finiteTiltDiracShell m).charpoly = X ^ 2 - C (m ^ 2 : ℝ)

/-- The finite tilt shell bridge owner target is closed. -/
theorem finiteTiltDiracShellBridgeOwnerTarget :
    FiniteTiltDiracShellBridgeOwnerTarget := by
  refine ⟨finiteTiltCurrentDensity_eq_boundaryCurrent, ?_⟩
  intro m
  exact ⟨finiteTiltDiracShell_sq m, finiteTiltBoundaryCurrent_sq_zero,
    finiteTiltDiracShell_eq_boundaryCurrent_add_mass m,
    finiteTiltDiracShell_trace m, finiteTiltDiracShell_det m,
    finiteTiltDiracShell_charpoly m⟩

end InfoGeometry.Clifford.FiniteTiltDiracShellBridge
