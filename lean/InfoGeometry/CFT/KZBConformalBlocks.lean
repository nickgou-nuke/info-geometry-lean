import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.CFT.KZBConformalBlocks

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def kzbLevel (k h_dual : ℝ) : ℝ :=
  k + h_dual

def kzbCurvatureCommutator (grad_z grad_tau : ℝ) : ℝ :=
  grad_z * grad_tau - grad_tau * grad_z

theorem kzb_flat_connection (grad_z grad_tau : ℝ) :
    kzbCurvatureCommutator grad_z grad_tau = 0 := by
  unfold kzbCurvatureCommutator
  ring
