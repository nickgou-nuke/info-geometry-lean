import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.GroupUnification.ParryEndpointCollapse

namespace Omega.GroupUnification

open Omega.GroupUnification.ParryEndpointCollapse

noncomputable section

def goldenMeanLegal : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => ¬ (a = true ∧ b = true) ∧ goldenMeanLegal (b :: t)

def parryLeft : Bool → ℝ
  | false => 1
  | true => Real.goldenRatio⁻¹

def parryRight : Bool → ℝ
  | false => Real.goldenRatio
  | true => 1

def parryInitial : Bool → ℝ
  | false => Real.goldenRatio / Real.sqrt 5
  | true => Real.goldenRatio⁻¹ / Real.sqrt 5

def parryTransition : Bool → Bool → ℝ
  | false, false => Real.goldenRatio⁻¹
  | false, true => Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹
  | true, false => 1
  | true, true => 0

private theorem goldenMeanLegal_tail {a b : Bool} {t : List Bool}
    (h : goldenMeanLegal (a :: b :: t)) : goldenMeanLegal (b :: t) :=
  h.2

private theorem goldenMeanLegal_adj {a b : Bool} {t : List Bool}
    (h : goldenMeanLegal (a :: b :: t)) : ¬ (a = true ∧ b = true) :=
  h.1

private theorem parryRight_ne_zero (a : Bool) : parryRight a ≠ 0 := by
  cases a with
  | false =>
      have hphi : (0 : ℝ) < Real.goldenRatio := by positivity
      exact ne_of_gt hphi
  | true =>
      simp [parryRight]

private theorem goldenRatio_ne_zero : (Real.goldenRatio : ℝ) ≠ 0 := by
  positivity

private theorem parryTransition_formula {a b : Bool} (h : ¬ (a = true ∧ b = true)) :
    parryTransition a b = parryRight b / (Real.goldenRatio * parryRight a) := by
  cases a <;> cases b
  · simp [parryTransition, parryRight]
  · simp [parryTransition, parryRight]
  · simp [parryTransition, parryRight]
    field_simp [goldenRatio_ne_zero]
  · exfalso
    exact h ⟨rfl, rfl⟩

private theorem parryInitial_formula (a : Bool) :
    parryInitial a = parryLeft a * parryRight a / Real.sqrt 5 := by
  cases a <;> simp [parryInitial, parryLeft, parryRight]

private theorem parryTransitionWeight_telescope :
    ∀ (a : Bool) (u : List Bool),
      goldenMeanLegal (a :: u) →
        transitionWeight parryTransition (a :: u) =
          parryRight (List.getLast (a :: u) (by simp)) /
            (parryRight a * Real.goldenRatio ^ u.length)
  | a, [], _ => by
      simp [transitionWeight, parryRight]
      exact (div_self (parryRight_ne_zero a)).symm
  | a, b :: t, hlegal => by
      have hadj : ¬ (a = true ∧ b = true) := goldenMeanLegal_adj hlegal
      have htail : goldenMeanLegal (b :: t) := goldenMeanLegal_tail hlegal
      rw [transitionWeight, parryTransition_formula hadj, parryTransitionWeight_telescope b t htail]
      simp
      field_simp [goldenRatio_ne_zero, parryRight_ne_zero a, parryRight_ne_zero b]
      ring

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Parry cylinder formula in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:exact-clock -/
theorem paper_zero_jitter_exact_clock (a : Bool) (u : List Bool)
    (hlegal : goldenMeanLegal (a :: u)) :
    cylinderWeight parryInitial parryTransition (a :: u) =
      parryLeft a * parryRight (List.getLast (a :: u) (by simp)) /
        (Real.sqrt 5 * Real.goldenRatio ^ u.length) := by
  have hsqrt5_ne_zero : (Real.sqrt 5 : ℝ) ≠ 0 := by
    have hsqrt5_pos : (0 : ℝ) < Real.sqrt 5 := by positivity
    exact ne_of_gt hsqrt5_pos
  rw [cylinderWeight, parryInitial_formula, parryTransitionWeight_telescope a u hlegal]
  field_simp [goldenRatio_ne_zero, hsqrt5_ne_zero, parryRight_ne_zero a]

end
end Omega.GroupUnification
