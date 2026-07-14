import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# InfoGeometry.Foundations.NewtonKantorovichBase

Algebraic base lemmas for Newton--Kantorovich majorant arguments.
-/

namespace NewtonKantorovichBase

noncomputable section

/-- Kantorovich majorant polynomial: `P(t) = (L/2) t² - t + η`. -/
def P (L η t : ℝ) : ℝ :=
  (L / 2) * t^2 - t + η

/-- Derivative of the majorant polynomial: `P'(t) = L t - 1`. -/
def P_deriv (L t : ℝ) : ℝ :=
  L * t - 1

/-- Discriminant of `(L/2)t² - t + η`: `1 - 2Lη`. -/
def discriminant (L η : ℝ) : ℝ :=
  1 - 2 * L * η

/--
Kantorovich threshold `L*η ≤ 1/2` iff discriminant is nonnegative.
-/
theorem kantorovich_condition_iff_discriminant_nonneg (L η : ℝ) :
    L * η ≤ 1 / 2 ↔ 0 ≤ discriminant L η := by
  unfold discriminant
  constructor <;> intro h <;> linarith

/--
If `L t*² - 2 t* + 2 η = 0`, then `P(L,η,t*) = 0`.
-/
theorem is_root_of_quadratic_form (L η t_star : ℝ)
    (h_quad : L * t_star^2 - 2 * t_star + 2 * η = 0) :
    P L η t_star = 0 := by
  unfold P
  calc
    (L / 2) * t_star^2 - t_star + η
        = (L * t_star^2 - 2 * t_star + 2 * η) / 2 := by ring
    _ = 0 / 2 := by rw [h_quad]
    _ = 0 := by ring

/--
Clean algebraic Newton-step identity for the majorant form.
-/
theorem newton_step_identity_clean (L η t : ℝ) (h_denom : 1 - L * t ≠ 0) :
    t + ((L / 2) * t^2 - t + η) / (1 - L * t) =
      (η - (L / 2) * t^2) / (1 - L * t) := by
  have hden' : 1 - t * L ≠ 0 := by simpa [mul_comm] using h_denom
  have hden'' : 1 - L * t = 1 - t * L := by ring
  rw [hden'']
  field_simp [hden']
  ring

/--
Equivalent Newton-step identity with `t - P/P'`.
-/
theorem newton_step_identity (L η t : ℝ) (h_deriv : P_deriv L t ≠ 0) :
    t - (P L η t) / (P_deriv L t) =
      (η - (L / 2) * t^2) / (1 - L * t) := by
  unfold P_deriv at *
  have hden : 1 - L * t ≠ 0 := by
    intro h
    apply h_deriv
    linarith
  have hlt : L * t - 1 = -(1 - L * t) := by ring
  rw [hlt, div_neg, sub_neg_eq_add]
  exact newton_step_identity_clean L η t hden

/--
Requested equivalent Newton-step form:
`t - P/P' = ((L/2)t² - η) / (L*t - 1)`.
-/
theorem newton_step_identity_requested_form (L η t : ℝ) (h_deriv : P_deriv L t ≠ 0) :
    t - (P L η t) / (P_deriv L t) =
      (((L / 2) * t^2) - η) / (L * t - 1) := by
  have hmain := newton_step_identity L η t h_deriv
  have hden0 : 1 - L * t ≠ 0 := by
    intro h
    apply h_deriv
    unfold P_deriv
    linarith
  have hden1 : L * t - 1 ≠ 0 := by
    intro h
    apply hden0
    linarith
  have hfrac :
      (η - (L / 2) * t^2) / (1 - L * t) =
        (((L / 2) * t^2) - η) / (L * t - 1) := by
    field_simp [hden0, hden1]
    ring
  calc
    t - (P L η t) / (P_deriv L t)
        = (η - (L / 2) * t^2) / (1 - L * t) := hmain
    _ = (((L / 2) * t^2) - η) / (L * t - 1) := hfrac

end
end NewtonKantorovichBase
