import Mathlib
import InfoGeometry.Canonical.LocalZornProjectiveAction

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open scoped LinearAlgebra.Projectivization

/-!
Continuity of the fixed local `SL₂(ℝ)` action for the canonical quotient
topology on the projectivization.  This is a fixed-element statement; joint
continuity in the matrix parameter is deliberately a separate layer.
-/

instance realProjectiveBoundarySetoid : Setoid {v : Fin 2 → ℝ // v ≠ 0} :=
  projectivizationSetoid ℝ (Fin 2 → ℝ)

noncomputable instance realProjectiveBoundaryTopology :
    TopologicalSpace RealProjectiveBoundary :=
  TopologicalSpace.coinduced
    (Quotient.mk' : {v : Fin 2 → ℝ // v ≠ 0} → RealProjectiveBoundary)
    inferInstance

theorem continuous_localSL2ProjectiveAction (g : SL2R) :
    Continuous (localSL2ProjectiveAction g) := by
  unfold localSL2ProjectiveAction
  unfold Projectivization.map
  apply Continuous.quotient_map'
  · fun_prop

theorem continuous_modularBoostProjectiveAction (s : ℝ) :
    Continuous (modularBoostProjectiveAction s) := by
  exact continuous_localSL2ProjectiveAction (modularBoostSL2 s)

end InfoGeometry.Canonical
