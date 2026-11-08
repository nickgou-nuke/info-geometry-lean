/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

theorem scalarDilationTopologicalColimitAction_right_inverse (t : ℝ) :
    scalarDilationTopologicalColimitAction t ≫
        scalarDilationTopologicalColimitAction (-t) =
      𝟙 topologicalColimit := by
  rw [← scalarDilationTopologicalColimitAction_add (-t) t]
  simpa using scalarDilationTopologicalColimitAction_zero

end InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction
