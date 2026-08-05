import Mathlib
import InfoGeometry.Canonical.SplitOctonionKleinFourTriality

namespace InfoGeometry.Canonical

open Real

/-- The logit function mapping probabilities in (0, 1) to ℝ. -/
noncomputable def logit (p : ℝ) : ℝ :=
  Real.log (p / (1 - p))

/-- The standard logistic sigmoid function, inverse of logit. -/
noncomputable def sigmoid (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

/-- The Bayesian likelihood-ratio update for a binary hypothesis. -/
noncomputable def bayesUpdate (Λ : ℝ) (p : ℝ) : ℝ :=
  (Λ * p) / (1 + (Λ - 1) * p)

/-- The translation by `τ` in log-odds space. -/
noncomputable def translation (τ η : ℝ) : ℝ :=
  η + τ

theorem logit_bayesUpdate (Λ p : ℝ) (hΛ : 0 < Λ) (hp : 0 < p) (hp1 : p < 1) :
    logit (bayesUpdate Λ p) = logit p + Real.log Λ := by
  dsimp [logit, bayesUpdate]
  have h_den : 1 + (Λ - 1) * p ≠ 0 := by
    have : 1 + (Λ - 1) * p > 0 := by nlinarith
    exact ne_of_gt this
  have h1 : 1 - (Λ * p) / (1 + (Λ - 1) * p) = (1 - p) / (1 + (Λ - 1) * p) := by
    rw [sub_eq_iff_eq_add]
    have : (1 - p) / (1 + (Λ - 1) * p) + (Λ * p) / (1 + (Λ - 1) * p) = (1 - p + Λ * p) / (1 + (Λ - 1) * p) := by rw [add_div]
    rw [this]
    have : 1 - p + Λ * p = 1 + (Λ - 1) * p := by ring
    rw [this, div_self h_den]
  rw [h1]
  rw [div_div_div_cancel_right₀ h_den]
  have hp2 : 1 - p > 0 := by linarith
  have hp3 : p / (1 - p) > 0 := div_pos hp hp2
  have h3 : Real.log ((Λ * p) / (1 - p)) = Real.log (p / (1 - p)) + Real.log Λ := by
    have eq_mul : (Λ * p) / (1 - p) = Λ * (p / (1 - p)) := by ring
    rw [eq_mul, Real.log_mul (ne_of_gt hΛ) (ne_of_gt hp3), add_comm]
  rw [h3]

/-- A minimal split octonion norm encoding for the evidence gap.
    We assert the mathematical relation structurally. -/
noncomputable def evidenceGapEncode (N_O ε : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(N_O / ε)))

theorem splitNorm_encode_logit (N_O ε : ℝ) (hε : 0 < ε) :
    N_O = ε * logit (evidenceGapEncode N_O ε) := by
  dsimp [evidenceGapEncode, logit]
  have h_den : 1 + Real.exp (-(N_O / ε)) ≠ 0 := by
    have : 1 + Real.exp (-(N_O / ε)) > 0 := by positivity
    exact ne_of_gt this
  have h1 : 1 - 1 / (1 + Real.exp (-(N_O / ε))) = Real.exp (-(N_O / ε)) / (1 + Real.exp (-(N_O / ε))) := by
    rw [sub_eq_iff_eq_add]
    have : Real.exp (-(N_O / ε)) / (1 + Real.exp (-(N_O / ε))) + 1 / (1 + Real.exp (-(N_O / ε))) = (Real.exp (-(N_O / ε)) + 1) / (1 + Real.exp (-(N_O / ε))) := by rw [add_div]
    rw [this]
    have : Real.exp (-(N_O / ε)) + 1 = 1 + Real.exp (-(N_O / ε)) := by ring
    rw [this, div_self h_den]
  rw [h1]
  rw [div_div_div_cancel_right₀ h_den, one_div, Real.log_inv, Real.log_exp, neg_neg]
  exact (mul_div_cancel₀ N_O (ne_of_gt hε)).symm

-- 2. and 3. The natural logarithmic coordinate

noncomputable def naturalCoordinate (a b X B : ℝ) : ℝ :=
  (1 / a) * Real.log ((a * X + b) / (a * B + b))

theorem naturalCoordinate_eq_logit (a b X B : ℝ) (h_den1 : a * X + a * B + 2 * b ≠ 0) :
    naturalCoordinate a b X B = (1 / a) * logit ((a * X + b) / (a * X + a * B + 2 * b)) := by
  dsimp [naturalCoordinate, logit]
  congr 2
  have h1 : 1 - (a * X + b) / (a * X + a * B + 2 * b) = (a * B + b) / (a * X + a * B + 2 * b) := by
    have h_eq : (1 : ℝ) = (a * X + a * B + 2 * b) / (a * X + a * B + 2 * b) := (div_self h_den1).symm
    rw [h_eq]
    rw [← sub_div]
    congr 1
    ring
  rw [h1]
  exact (div_div_div_cancel_right₀ h_den1 (a * X + b) (a * B + b)).symm

-- 10, 11, 12. Recursive online background estimator

noncomputable def updateSum (ρ S_prev r X : ℝ) : ℝ :=
  ρ * S_prev + r * X

noncomputable def updateMass (ρ N_prev r : ℝ) : ℝ :=
  ρ * N_prev + r

noncomputable def updateBackground (S N : ℝ) : ℝ :=
  S / N

theorem barycentric_update (ρ S_prev N_prev r X B_prev : ℝ)
    (hB : B_prev = S_prev / N_prev)
    (hN : ρ * N_prev + r ≠ 0)
    (hN_prev : N_prev ≠ 0) :
    updateBackground (updateSum ρ S_prev r X) (updateMass ρ N_prev r) =
      B_prev + (r / (ρ * N_prev + r)) * (X - B_prev) := by
  dsimp [updateBackground, updateSum, updateMass]
  rw [hB]
  have h1 : S_prev / N_prev + (r / (ρ * N_prev + r)) * (X - S_prev / N_prev) = (S_prev / N_prev * (ρ * N_prev + r) + r * (X - S_prev / N_prev)) / (ρ * N_prev + r) := by
    have h_eq : S_prev / N_prev = (S_prev / N_prev * (ρ * N_prev + r)) / (ρ * N_prev + r) := by
      rw [mul_div_cancel_right₀ _ hN]
    nth_rw 1 [h_eq]
    have h_mul : (r / (ρ * N_prev + r)) * (X - S_prev / N_prev) = (r * (X - S_prev / N_prev)) / (ρ * N_prev + r) := by ring
    rw [h_mul, add_div]
  rw [h1]
  congr 1
  calc
    ρ * S_prev + r * X = S_prev * ρ + r * X := by ring
    _ = (S_prev / N_prev * N_prev) * ρ + r * X := by rw [div_mul_cancel₀ S_prev hN_prev]
    _ = (S_prev / N_prev) * (N_prev * ρ) + r * X := by ring
    _ = (S_prev / N_prev) * (ρ * N_prev) + (S_prev / N_prev) * r + r * X - r * (S_prev / N_prev) := by ring
    _ = S_prev / N_prev * (ρ * N_prev + r) + r * (X - S_prev / N_prev) := by ring

theorem logit_sigmoid (x : ℝ) :
    logit (sigmoid x) = x := by
  dsimp [sigmoid, logit]
  have h_den : 1 + Real.exp (-x) > 0 := by positivity
  have h1 : 1 - 1 / (1 + Real.exp (-x)) = Real.exp (-x) / (1 + Real.exp (-x)) := by
    have h_eq : (1 : ℝ) = (1 + Real.exp (-x)) / (1 + Real.exp (-x)) := (div_self (ne_of_gt h_den)).symm
    nth_rw 1 [h_eq]
    rw [← sub_div]
    congr 1
    ring
  rw [h1]
  have h2 : (1 / (1 + Real.exp (-x))) / (Real.exp (-x) / (1 + Real.exp (-x))) = 1 / Real.exp (-x) := by
    exact div_div_div_cancel_right₀ (ne_of_gt h_den) 1 (Real.exp (-x))
  rw [h2, one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem sigmoid_logit (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sigmoid (logit p) = p := by
  dsimp [sigmoid, logit]
  rw [Real.exp_neg]
  have hp_div : p / (1 - p) > 0 := by
    apply div_pos hp0
    linarith
  rw [Real.exp_log hp_div]
  have h2 : (p / (1 - p))⁻¹ = (1 - p) / p := by rw [inv_div]
  rw [h2]
  have h3 : 1 + (1 - p) / p = 1 / p := by
    have h_eq : (1 : ℝ) = p / p := (div_self (ne_of_gt hp0)).symm
    nth_rw 1 [h_eq]
    rw [← add_div]
    congr 1
    ring
  rw [h3, one_div, one_div, inv_inv]

/-- The one-parameter Möbius flow theorem. -/
noncomputable def bayesFlow (τ p : ℝ) : ℝ :=
  bayesUpdate (Real.exp τ) p

theorem bayesFlow_zero (p : ℝ) :
    bayesFlow 0 p = p := by
  dsimp [bayesFlow, bayesUpdate]
  rw [Real.exp_zero]
  ring_nf

theorem bayesFlow_eq_sigmoid (τ p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    bayesFlow τ p = sigmoid (logit p + τ) := by
  have h_exp_pos : 0 < Real.exp τ := Real.exp_pos τ
  have h_logit := logit_bayesUpdate (Real.exp τ) p h_exp_pos hp0 hp1
  have h_apply : sigmoid (logit (bayesFlow τ p)) = sigmoid (logit p + τ) := by
    have : logit (bayesFlow τ p) = logit (bayesUpdate (Real.exp τ) p) := rfl
    rw [this, h_logit, Real.log_exp]
  have h_den : 1 - p + p * Real.exp τ > 0 := add_pos (sub_pos.mpr hp1) (mul_pos hp0 h_exp_pos)
  have h_num : Real.exp τ * p > 0 := mul_pos h_exp_pos hp0
  have h_pos : 0 < bayesFlow τ p := by
    dsimp [bayesFlow, bayesUpdate]
    have h_den2 : 1 + (Real.exp τ - 1) * p = 1 - p + p * Real.exp τ := by ring
    rw [h_den2]
    exact div_pos h_num h_den
  have h_lt1 : bayesFlow τ p < 1 := by
    dsimp [bayesFlow, bayesUpdate]
    have h_den2 : 1 + (Real.exp τ - 1) * p = 1 - p + p * Real.exp τ := by ring
    rw [h_den2]
    rw [div_lt_one h_den]
    have : Real.exp τ * p = p * Real.exp τ := mul_comm _ _
    rw [this]
    linarith
  have h_cancel := sigmoid_logit (bayesFlow τ p) h_pos h_lt1
  rw [← h_cancel]
  exact h_apply

theorem bayesFlow_add (τ₁ τ₂ p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    bayesFlow (τ₁ + τ₂) p = bayesFlow τ₁ (bayesFlow τ₂ p) := by
  rw [bayesFlow_eq_sigmoid (τ₁ + τ₂) p hp0 hp1]
  have h_pos : 0 < bayesFlow τ₂ p := by
    have h_exp_pos : 0 < Real.exp τ₂ := Real.exp_pos τ₂
    have h_den : 1 - p + p * Real.exp τ₂ > 0 := add_pos (sub_pos.mpr hp1) (mul_pos hp0 h_exp_pos)
    dsimp [bayesFlow, bayesUpdate]
    have h_den2 : 1 + (Real.exp τ₂ - 1) * p = 1 - p + p * Real.exp τ₂ := by ring
    rw [h_den2]
    exact div_pos (mul_pos h_exp_pos hp0) h_den
  have h_lt1 : bayesFlow τ₂ p < 1 := by
    have h_exp_pos : 0 < Real.exp τ₂ := Real.exp_pos τ₂
    have h_den : 1 - p + p * Real.exp τ₂ > 0 := add_pos (sub_pos.mpr hp1) (mul_pos hp0 h_exp_pos)
    dsimp [bayesFlow, bayesUpdate]
    have h_den2 : 1 + (Real.exp τ₂ - 1) * p = 1 - p + p * Real.exp τ₂ := by ring
    rw [h_den2]
    rw [div_lt_one h_den]
    have : Real.exp τ₂ * p = p * Real.exp τ₂ := mul_comm _ _
    rw [this]
    linarith
  rw [bayesFlow_eq_sigmoid τ₁ (bayesFlow τ₂ p) h_pos h_lt1]
  rw [bayesFlow_eq_sigmoid τ₂ p hp0 hp1]
  rw [logit_sigmoid (logit p + τ₂)]
  have h_assoc : logit p + (τ₁ + τ₂) = logit p + τ₂ + τ₁ := by ring
  rw [h_assoc]

/-- The affine quasi-deviance model for CMOS sensor noise with variance V(μ) = aμ + b. -/
noncomputable def affineDeviance (a b x μ : ℝ) : ℝ :=
  (2 / a^2) * ((a * x + b) * Real.log ((a * x + b) / (a * μ + b)) - a * (x - μ))

/-- The quasi-deviance is exactly zero when the observation matches the reference. -/
theorem affineDeviance_self (a b μ : ℝ) (h_pos : a * μ + b > 0) :
    affineDeviance a b μ μ = 0 := by
  dsimp [affineDeviance]
  have h_div : (a * μ + b) / (a * μ + b) = 1 := div_self (ne_of_gt h_pos)
  rw [h_div, Real.log_one]
  ring

end InfoGeometry.Canonical

