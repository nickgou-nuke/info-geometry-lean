import InfoGeometry.Clifford.FiniteTiltDiracShell
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.FiniteTiltDiracShellBridge

Thin bridge exports for the finite tilt Dirac shell.
-/

namespace InfoGeometry.Clifford.FiniteTiltDiracShellBridge

open FiniteTiltDiracShell

/-- Combined concrete shell-square and boundary-current theorem. -/
@[rep_depth operator]
theorem finiteTiltDiracShellBridge_properties :
  (
    ∀ m : ℝ,
      finiteTiltDiracShell m * finiteTiltDiracShell m =
        (m ^ 2 : ℝ) • (1 : Mat2)
  ) ∧
  finiteTiltCurrentDensity = finiteTiltBoundaryCurrent :=
  ⟨finiteTiltDiracShell_sq, finiteTiltCurrentDensity_eq_boundaryCurrent⟩

end InfoGeometry.Clifford.FiniteTiltDiracShellBridge
