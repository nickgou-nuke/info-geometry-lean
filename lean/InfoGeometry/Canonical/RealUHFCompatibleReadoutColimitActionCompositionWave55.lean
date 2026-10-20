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

theorem scalarDilationTopologicalColimitAction_comp_forward (s t : ℝ) :
    scalarDilationTopologicalColimitAction s ≫
        scalarDilationTopologicalColimitAction t =
      scalarDilationTopologicalColimitAction (s + t) := by
  calc
    scalarDilationTopologicalColimitAction s ≫
        scalarDilationTopologicalColimitAction t =
      scalarDilationTopologicalColimitAction (t + s) := by
        exact (scalarDilationTopologicalColimitAction_add t s).symm
    _ = scalarDilationTopologicalColimitAction (s + t) := by
      rw [add_comm]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction
