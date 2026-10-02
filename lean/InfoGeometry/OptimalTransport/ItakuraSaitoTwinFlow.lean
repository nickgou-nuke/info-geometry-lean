import InfoGeometry.InformationGeometry.ItakuraSaitoBregmanBridge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace InfoGeometry.OptimalTransport.ItakuraSaitoTwinFlow

open InfoGeometry.InformationGeometry.ItakuraSaito

def potential (state : ℝ) : ℝ :=
  isDivergence state (1 - state)

def gradient (state : ℝ) : ℝ :=
  (2 * state - 1) / (state * (1 - state) ^ 2)

theorem potential_nonneg {state : ℝ} (valid : state ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ potential state :=
  isDivergence_nonneg state (1 - state) valid.1 (sub_pos.mpr valid.2)

@[simp] theorem potential_half : potential (1 / 2) = 0 := by
  norm_num [potential, isDivergence]

theorem potential_pos_of_ne_half {state : ℝ}
    (valid : state ∈ Set.Ioo (0 : ℝ) 1) (offCenter : state ≠ 1 / 2) :
    0 < potential state := by
  have complement_pos : 0 < 1 - state := sub_pos.mpr valid.2
  have ratio_ne_one : state / (1 - state) ≠ 1 := by
    intro equality
    have balance := (div_eq_one_iff_eq (ne_of_gt complement_pos)).mp equality
    exact offCenter (by linarith)
  have bound := Real.log_lt_sub_one_of_pos
    (div_pos valid.1 complement_pos) ratio_ne_one
  dsimp [potential, isDivergence]
  linarith

theorem potential_eq_zero_iff {state : ℝ} (valid : state ∈ Set.Ioo (0 : ℝ) 1) :
    potential state = 0 ↔ state = 1 / 2 := by
  constructor
  · intro equality
    by_contra offCenter
    have positive := potential_pos_of_ne_half valid offCenter
    linarith
  · rintro rfl
    exact potential_half

theorem hasDerivAt_potential {state : ℝ} (valid : state ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt potential (gradient state) state := by
  have complement_pos : 0 < 1 - state := sub_pos.mpr valid.2
  have complement_ne := ne_of_gt complement_pos
  have state_ne := ne_of_gt valid.1
  have ratio_derivative :
      HasDerivAt (fun value : ℝ => value / (1 - value))
        (1 / (1 - state) ^ 2) state := by
    convert (hasDerivAt_id state).div
      ((hasDerivAt_const state (1 : ℝ)).sub (hasDerivAt_id state)) complement_ne
      using 1 <;> ring_nf
  have logarithm_derivative := ratio_derivative.log
    (ne_of_gt (div_pos valid.1 complement_pos))
  have derivative := (ratio_derivative.sub logarithm_derivative).sub_const 1
  change HasDerivAt
    (fun value : ℝ => value / (1 - value) - Real.log (value / (1 - value)) - 1)
    (gradient state) state
  convert derivative using 1
  dsimp [gradient]
  field_simp [state_ne, complement_ne] <;> ring_nf

theorem deriv_potential {state : ℝ} (valid : state ∈ Set.Ioo (0 : ℝ) 1) :
    deriv potential state = gradient state :=
  (hasDerivAt_potential valid).deriv

theorem gradient_eq_zero_iff {state : ℝ} (valid : state ∈ Set.Ioo (0 : ℝ) 1) :
    gradient state = 0 ↔ state = 1 / 2 := by
  have denominator_pos : 0 < state * (1 - state) ^ 2 :=
    mul_pos valid.1 (sq_pos_of_pos (sub_pos.mpr valid.2))
  simp only [gradient, div_eq_zero_iff, ne_of_gt denominator_pos, or_false]
  constructor <;> intro equality <;> linarith

@[simp] theorem gradient_half : gradient (1 / 2) = 0 := by
  norm_num [gradient]

theorem energy_derivative_along_descent {trajectory : ℝ → ℝ} {time : ℝ}
    (valid : trajectory time ∈ Set.Ioo (0 : ℝ) 1)
    (velocity : HasDerivAt trajectory (-gradient (trajectory time)) time) :
    HasDerivAt (fun instant => potential (trajectory instant))
      (-(gradient (trajectory time)) ^ 2) time := by
  convert (hasDerivAt_potential valid).comp time velocity using 1 <;> ring

theorem energy_deriv_nonpos {trajectory : ℝ → ℝ} {time : ℝ}
    (valid : trajectory time ∈ Set.Ioo (0 : ℝ) 1)
    (velocity : HasDerivAt trajectory (-gradient (trajectory time)) time) :
    deriv (fun instant => potential (trajectory instant)) time ≤ 0 := by
  rw [(energy_derivative_along_descent valid velocity).deriv]
  exact neg_nonpos.mpr (sq_nonneg _)

def perturbedFlow (residual : ℝ → ℝ) (state : ℝ) : ℝ :=
  -gradient state + residual state

@[simp] theorem perturbedFlow_half (residual : ℝ → ℝ) :
    perturbedFlow residual (1 / 2) = residual (1 / 2) := by
  rw [perturbedFlow, gradient_half]
  simp

theorem half_equilibrium_iff (residual : ℝ → ℝ) :
    perturbedFlow residual (1 / 2) = 0 ↔ residual (1 / 2) = 0 := by
  rw [perturbedFlow_half]

end InfoGeometry.OptimalTransport.ItakuraSaitoTwinFlow
