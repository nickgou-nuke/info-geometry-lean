import Mathlib
import InfoGeometry.Canonical.BayesianMoebius

namespace InfoGeometry.Canonical

open Real

/-- The q-logarithm. -/
noncomputable def qLog (q x : ℝ) : ℝ :=
  if q = 1 then Real.log x else (x^(1 - q) - 1) / (1 - q)

/-- The q-exponential. -/
noncomputable def qExp (q x : ℝ) : ℝ :=
  if q = 1 then Real.exp x else (max (1 + (1 - q) * x) 0)^(1 / (1 - q))

/-- The generalized q-product. -/
noncomputable def qProd (q x y : ℝ) : ℝ :=
  if q = 1 then x * y else (max (x^(1 - q) + y^(1 - q) - 1) 0)^(1 / (1 - q))

/-- On the valid domain, qLog (qExp x) = x. -/
theorem qLog_qExp_self {q x : ℝ} (hq : q ≠ 1) (h_dom : 1 + (1 - q) * x > 0) :
    qLog q (qExp q x) = x := by
  dsimp [qLog, qExp]
  rw [if_neg hq, if_neg hq]
  have h_max : max (1 + (1 - q) * x) 0 = 1 + (1 - q) * x := max_eq_left (le_of_lt h_dom)
  rw [h_max]
  have h_pow : ((1 + (1 - q) * x) ^ (1 / (1 - q))) ^ (1 - q) = 1 + (1 - q) * x := by
    rw [← Real.rpow_mul (le_of_lt h_dom)]
    have h_inv : (1 / (1 - q)) * (1 - q) = 1 := by
      exact one_div_mul_cancel (sub_ne_zero.mpr hq.symm)
    rw [h_inv, Real.rpow_one]
  rw [h_pow]
  have h1 : 1 + (1 - q) * x - 1 = (1 - q) * x := by ring
  rw [h1]
  exact mul_div_cancel_left₀ x (sub_ne_zero.mpr hq.symm)

/-- Additivity of q-logarithm over q-product. -/
theorem qLog_qProd {q x y : ℝ} (hq : q ≠ 1) (hx : x > 0) (hy : y > 0)
    (h_dom : x^(1 - q) + y^(1 - q) - 1 > 0) :
    qLog q (qProd q x y) = qLog q x + qLog q y := by
  dsimp [qLog, qProd]
  repeat rw [if_neg hq]
  have h_max : max (x^(1 - q) + y^(1 - q) - 1) 0 = x^(1 - q) + y^(1 - q) - 1 := max_eq_left (le_of_lt h_dom)
  rw [h_max]
  have h_pow : ((x^(1 - q) + y^(1 - q) - 1) ^ (1 / (1 - q))) ^ (1 - q) = x^(1 - q) + y^(1 - q) - 1 := by
    rw [← Real.rpow_mul (le_of_lt h_dom)]
    have h_inv : (1 / (1 - q)) * (1 - q) = 1 := one_div_mul_cancel (sub_ne_zero.mpr hq.symm)
    rw [h_inv, Real.rpow_one]
  rw [h_pow]
  ring_nf

end InfoGeometry.Canonical
