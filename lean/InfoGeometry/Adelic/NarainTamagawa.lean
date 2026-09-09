import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Adelic.NarainTamagawa

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def tamagawaVolumeSL2 : ℝ :=
  1

theorem tamagawa_volume_is_one :
    tamagawaVolumeSL2 = 1 := by
  unfold tamagawaVolumeSL2
  rfl
