import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.LightCone.ChiralPrimeDecomposition

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def chiralLeftGen (d_chi d_theta : ℝ) : ℝ :=
  (1 / 2) * (d_chi + d_theta)

def chiralRightGen (d_chi d_theta : ℝ) : ℝ :=
  (1 / 2) * (d_chi - d_theta)

theorem angular_generator_decomposition (d_chi d_theta : ℝ) :
    chiralLeftGen d_chi d_theta - chiralRightGen d_chi d_theta = d_theta := by
  unfold chiralLeftGen chiralRightGen
  ring

theorem scaling_generator_decomposition (d_chi d_theta : ℝ) :
    chiralLeftGen d_chi d_theta + chiralRightGen d_chi d_theta = d_chi := by
  unfold chiralLeftGen chiralRightGen
  ring
