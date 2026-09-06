import Mathlib

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
  unfold laurentPoleLogPotential
  have hlog :
      HasDerivAt (fun x : ℝ => Real.log (x - 1)) ((β - 1)⁻¹) β := by
    simpa using (Real.hasDerivAt_log (sub_ne_zero.mpr hβ)).comp β
      ((hasDerivAt_id β).sub_const 1)
  simpa using hlog.neg.deriv

theorem pole_log_second_derivative {β : ℝ} (hβ : β ≠ 1) :
    heatCapacityKernel β = ((β - 1) ^ 2)⁻¹ := by
  unfold heatCapacityKernel laurentPoleGradient
  have hinv :
      HasDerivAt (fun x : ℝ => (x - 1)⁻¹) (-((β - 1) ^ 2)⁻¹) β := by
    simpa [pow_two] using
      (hasDerivAt_inv (sub_ne_zero.mpr hβ)).comp β
        ((hasDerivAt_id β).sub_const 1)
  have hneg :
      HasDerivAt (fun x : ℝ => -((x - 1)⁻¹)) (((β - 1) ^ 2)⁻¹) β := by
    simpa [neg_neg] using hinv.neg
  simpa using hneg.deriv

/-- Consolidated finite phase-transition package. -/
theorem phase_transition_susy_synthesis (zeta : ℂ → ℂ) (βc : ℂ) (β : ℝ)
    (hz : zeta βc ≠ 0) (hβ : β ≠ 1) :
    TotalSUSYPartition zeta βc = 1 ∧
    laurentPolePartition β * mobiusFermionRegulator β = 1 ∧
    heatCapacityKernel β = ((β - 1) ^ 2)⁻¹ := by
  exact ⟨susy_vacuum_regularization zeta βc hz,
    pole_partition_regularized hβ, pole_log_second_derivative hβ⟩

end noncomputable section
