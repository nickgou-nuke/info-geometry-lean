import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.CFT.ModularInvariance

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def modularS (τ : ℂ) : ℂ :=
  - 1 / τ

def modularT (τ : ℂ) : ℂ :=
  τ + 1

theorem modular_S_involution (τ : ℂ) (hτ : τ ≠ 0) :
    modularS (modularS τ) = τ := by
  unfold modularS
  field_simp [hτ]
