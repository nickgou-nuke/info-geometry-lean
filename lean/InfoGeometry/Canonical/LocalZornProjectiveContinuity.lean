import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LocalZornProjectiveAction
import InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

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
  exact InfoGeometry.Twistor.ProjectiveNullConfigurationTopology.projectivization_map_continuous
    g.toLin'.toLinearMap g.toLin'.injective (by fun_prop)

theorem continuous_modularBoostProjectiveAction (s : ℝ) :
    Continuous (modularBoostProjectiveAction s) := by
  exact continuous_localSL2ProjectiveAction (modularBoostSL2 s)

end InfoGeometry.Canonical
