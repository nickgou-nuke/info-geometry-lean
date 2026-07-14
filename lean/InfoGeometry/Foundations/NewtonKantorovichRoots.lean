import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import InfoGeometry.Foundations.NewtonKantorovichBase

/-!
# InfoGeometry.Foundations.NewtonKantorovichRoots

Explicit majorant roots for the Newton--Kantorovich scalar polynomial.
-/

namespace NewtonKantorovichRoots

open InfoGeometry.Foundations.NewtonKantorovichBase

noncomputable section

/-- `√Δ` where `Δ = 1 - 2Lη`. -/
def sqrtDiscriminant (L η : ℝ) : ℝ :=
  Real.sqrt (discriminant L η)

/-- Small root of `(L/2)t² - t + η = 0` (for `L ≠ 0`). -/
def tMinus (L η : ℝ) : ℝ :=
  (1 - sqrtDiscriminant L η) / L

/-- Large root of `(L/2)t² - t + η = 0` (for `L ≠ 0`). -/
def tPlus (L η : ℝ) : ℝ :=
  (1 + sqrtDiscriminant L η) / L

theorem two_mul_L_mul_tMinus (L η : ℝ) (hL : L ≠ 0) :
    2 * L * tMinus L η = 2 - 2 * sqrtDiscriminant L η := by
  unfold tMinus
  field_simp [hL]

theorem two_mul_L_mul_tPlus (L η : ℝ) (hL : L ≠ 0) :
    2 * L * tPlus L η = 2 + 2 * sqrtDiscriminant L η := by
  unfold tPlus
  field_simp [hL]

/-- The quadratic-form equation at `tMinus`. -/
theorem tMinus_quadratic_form (L η : ℝ) (hL : L ≠ 0) (hΔ : 0 ≤ discriminant L η) :
    L * (tMinus L η)^2 - 2 * tMinus L η + 2 * η = 0 := by
  have hsq : (sqrtDiscriminant L η)^2 = discriminant L η := by
    unfold sqrtDiscriminant
    exact Real.sq_sqrt hΔ
  unfold tMinus
  field_simp [hL]
  ring_nf
  rw [hsq]
  unfold discriminant
  ring

/-- The quadratic-form equation at `tPlus`. -/
theorem tPlus_quadratic_form (L η : ℝ) (hL : L ≠ 0) (hΔ : 0 ≤ discriminant L η) :
    L * (tPlus L η)^2 - 2 * tPlus L η + 2 * η = 0 := by
  have hsq : (sqrtDiscriminant L η)^2 = discriminant L η := by
    unfold sqrtDiscriminant
    exact Real.sq_sqrt hΔ
  unfold tPlus
  field_simp [hL]
  ring_nf
  rw [hsq]
  unfold discriminant
  ring

/-- `tMinus` is a root of `P`. -/
theorem P_tMinus_eq_zero (L η : ℝ) (hL : L ≠ 0) (hΔ : 0 ≤ discriminant L η) :
    P L η (tMinus L η) = 0 :=
  is_root_of_quadratic_form L η (tMinus L η) (tMinus_quadratic_form L η hL hΔ)

/-- `tPlus` is a root of `P`. -/
theorem P_tPlus_eq_zero (L η : ℝ) (hL : L ≠ 0) (hΔ : 0 ≤ discriminant L η) :
    P L η (tPlus L η) = 0 :=
  is_root_of_quadratic_form L η (tPlus L η) (tPlus_quadratic_form L η hL hΔ)

/-- Root ordering for positive `L`: `tMinus ≤ tPlus`. -/
theorem tMinus_le_tPlus (L η : ℝ) (hL : 0 < L) :
    tMinus L η ≤ tPlus L η := by
  unfold tMinus tPlus
  have hsqrt : 0 ≤ sqrtDiscriminant L η := by
    unfold sqrtDiscriminant
    exact Real.sqrt_nonneg _
  have hnum : 1 - sqrtDiscriminant L η ≤ 1 + sqrtDiscriminant L η := by linarith
  rw [div_le_iff₀ hL]
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hmul : ((1 + sqrtDiscriminant L η) / L) * L = 1 + sqrtDiscriminant L η := by
    rw [div_mul_cancel₀ _ hL0]
  rw [hmul]
  exact hnum

/-- Exact denominator value at the small root. -/
theorem one_sub_L_tMinus (L η : ℝ) (hL : L ≠ 0) :
    1 - L * tMinus L η = sqrtDiscriminant L η := by
  unfold tMinus
  field_simp [hL]
  ring

end
end NewtonKantorovichRoots
