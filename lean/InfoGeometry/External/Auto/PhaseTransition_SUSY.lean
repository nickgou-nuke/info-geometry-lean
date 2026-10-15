import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Phase Transition and Möbius/SUSY Regularization

Finite formal layer for the zeta-pole phase-transition dictionary.

The file proves two checkable pieces:

* for any nonzero zeta-like partition value, multiplying the bosonic sector
  by its fermionic inverse sector gives the regulated total partition `1`;
* in the Laurent pole chart `Z(β) = 1 / (β - 1)`, the second derivative of
  the log-potential `-log(β - 1)` is exactly `(β - 1)⁻²`.

This does not prove analytic facts about the Riemann zeta function.  The pole
chart is the local model around a simple pole with residue one.
-/

noncomputable section

set_option linter.unnecessarySimpa false

def BosonicPartition (zeta : ℂ → ℂ) (β : ℂ) : ℂ :=
  zeta β

def FermionicPartition (zeta : ℂ → ℂ) (β : ℂ) : ℂ :=
  (zeta β)⁻¹

def TotalSUSYPartition (zeta : ℂ → ℂ) (β : ℂ) : ℂ :=
  BosonicPartition zeta β * FermionicPartition zeta β

theorem susy_vacuum_regularization (zeta : ℂ → ℂ) (β : ℂ)
    (h : zeta β ≠ 0) :
    TotalSUSYPartition zeta β = 1 := by
  unfold TotalSUSYPartition BosonicPartition FermionicPartition
  exact mul_inv_cancel₀ h

def laurentPolePartition (β : ℝ) : ℝ :=
  (β - 1)⁻¹

def mobiusFermionRegulator (β : ℝ) : ℝ :=
  β - 1

def laurentPoleLogPotential (β : ℝ) : ℝ :=
  -Real.log (β - 1)

def laurentPoleGradient (β : ℝ) : ℝ :=
  -(β - 1)⁻¹

def heatCapacityKernel (β : ℝ) : ℝ :=
  deriv laurentPoleGradient β

theorem pole_partition_regularized {β : ℝ} (hβ : β ≠ 1) :
    laurentPolePartition β * mobiusFermionRegulator β = 1 := by
  unfold laurentPolePartition mobiusFermionRegulator
  field_simp [sub_ne_zero.mpr hβ]

theorem pole_log_first_derivative {β : ℝ} (hβ : β ≠ 1) :
    deriv laurentPoleLogPotential β = -(β - 1)⁻¹ := by
  have hlog := (Real.hasDerivAt_log (sub_ne_zero.mpr hβ)).comp β
    ((hasDerivAt_id β).sub_const 1)
  have hlog' : deriv (Real.log ∘ fun x : ℝ => x - 1) β =
      (β - 1)⁻¹ := by
    simpa using hlog.deriv
  change deriv (-(Real.log ∘ fun x : ℝ => x - 1)) β = _
  rw [deriv.neg, hlog']

/-- The ordinary logarithm is strictly concave on the positive real axis,
    hence `-log` is strictly convex there. This is the standard calculus fact
    behind the local pole potential. -/
theorem neg_log_strictConvexOn :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => -Real.log x) := by
  exact strictConcaveOn_log_Ioi.neg

theorem pole_log_second_derivative {β : ℝ} (hβ : β ≠ 1) :
    heatCapacityKernel β = ((β - 1) ^ 2)⁻¹ := by
  have hinv := (hasDerivAt_inv (sub_ne_zero.mpr hβ)).comp β
    ((hasDerivAt_id β).sub_const 1)
  have hinv' : deriv ((fun y : ℝ => y⁻¹) ∘ fun x => x - 1) β =
      -((β - 1) ^ 2)⁻¹ := by
    simpa using hinv.deriv
  change deriv (- ((fun y : ℝ => y⁻¹) ∘ fun x => x - 1)) β = _
  rw [deriv.neg, hinv']
  field_simp [sub_ne_zero.mpr hβ]

/-- Consolidated finite phase-transition package. -/
theorem phase_transition_susy_synthesis (zeta : ℂ → ℂ) (βc : ℂ) (β : ℝ)
    (hz : zeta βc ≠ 0) (hβ : β ≠ 1) :
    TotalSUSYPartition zeta βc = 1 ∧
    laurentPolePartition β * mobiusFermionRegulator β = 1 ∧
    heatCapacityKernel β = ((β - 1) ^ 2)⁻¹ := by
  exact ⟨susy_vacuum_regularization zeta βc hz,
    pole_partition_regularized hβ, pole_log_second_derivative hβ⟩

end noncomputable section
