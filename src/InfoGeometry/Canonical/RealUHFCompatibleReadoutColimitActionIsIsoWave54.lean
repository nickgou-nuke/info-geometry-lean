/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitActionInverseWave52
import InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitActionLeftInverseWave53

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

theorem scalarDilationTopologicalColimitAction_isIso (t : ℝ) :
    IsIso (scalarDilationTopologicalColimitAction t) := by
  refine IsIso.mk ⟨scalarDilationTopologicalColimitAction (-t), ?_, ?_⟩
  · exact scalarDilationTopologicalColimitAction_right_inverse t
  · exact scalarDilationTopologicalColimitAction_left_inverse t

end InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitAction
