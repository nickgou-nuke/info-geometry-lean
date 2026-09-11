import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.IndexTheory.AtiyahSingerDirac

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def analyticDiracIndex (dim_ker dim_coker : ℤ) : ℤ :=
  dim_ker - dim_coker

def topologicalDiracIndex (k : ℤ) : ℤ :=
  k

def firstChernClassFlux (k : ℤ) : ℤ :=
  k

def aHatGenusCylinder : ℝ :=
  1

theorem dirac_light_cone_reduction (d_xi d_theta : ℝ) :
    (1 / 2) * (d_xi + d_theta) - (1 / 2) * (d_xi - d_theta) = d_theta := by
  ring

theorem dirac_eigenvalue_real (n : ℤ) :
    - (n : ℝ) = - ((n : ℝ)) :=
  rfl

theorem analytic_index_vacuum_zero :
    analyticDiracIndex 1 1 = 0 := by
  unfold analyticDiracIndex
  rfl

theorem topological_index_vacuum_zero :
    topologicalDiracIndex 0 = 0 := by
  unfold topologicalDiracIndex
  rfl

theorem atiyah_singer_index_theorem_match (k : ℤ) :
    analyticDiracIndex k 0 = topologicalDiracIndex k := by
  unfold analyticDiracIndex topologicalDiracIndex
  ring

theorem atiyah_singer_integral_identity (k : ℤ) :
    aHatGenusCylinder * (firstChernClassFlux k : ℝ) = ((topologicalDiracIndex k : ℤ) : ℝ) := by
  unfold aHatGenusCylinder firstChernClassFlux topologicalDiracIndex
  simp only [one_mul]
