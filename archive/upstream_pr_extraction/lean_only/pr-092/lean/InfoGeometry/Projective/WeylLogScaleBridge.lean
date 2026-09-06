import Mathlib

/-!
# Positive Weyl scales and logarithmic coordinates

This owner formalizes the scalar Weyl layer only.  A positive scale has a
single-valued real logarithm; complex logarithmic monodromy is deliberately
left to the existing Klein period owners.
-/

namespace InfoGeometry.Projective.WeylLogScaleBridge

noncomputable section

abbrev PositiveScale := {x : ℝ // 0 < x}

def scaleLog (Ω : PositiveScale) : ℝ := Real.log Ω.1

theorem exp_scaleLog (Ω : PositiveScale) :
    Real.exp (scaleLog Ω) = Ω.1 := by
  exact Real.exp_log Ω.2

theorem scaleLog_mul (Ω₁ Ω₂ : PositiveScale) :
    scaleLog ⟨Ω₁.1 * Ω₂.1, mul_pos Ω₁.2 Ω₂.2⟩ =
      scaleLog Ω₁ + scaleLog Ω₂ := by
  unfold scaleLog
  rw [Real.log_mul (ne_of_gt Ω₁.2) (ne_of_gt Ω₂.2)]

def scaleOfLog (σ : ℝ) : PositiveScale :=
  ⟨Real.exp σ, Real.exp_pos σ⟩

theorem scaleLog_scaleOfLog (σ : ℝ) :
    scaleLog (scaleOfLog σ) = σ := by
  simp [scaleOfLog, scaleLog]

theorem scaleOfLog_scaleLog (Ω : PositiveScale) :
    scaleOfLog (scaleLog Ω) = Ω := by
  apply Subtype.ext
  exact exp_scaleLog Ω

def weylMetricAction (σ g : ℝ) : ℝ := Real.exp (2 * σ) * g

theorem weylMetricAction_add (σ τ g : ℝ) :
    weylMetricAction (σ + τ) g =
      weylMetricAction σ (weylMetricAction τ g) := by
  unfold weylMetricAction
  rw [mul_add, Real.exp_add]
  ring

def weylFieldAction (w σ Φ : ℝ) : ℝ := Real.exp (w * σ) * Φ

theorem weylFieldAction_add (w σ τ Φ : ℝ) :
    weylFieldAction w (σ + τ) Φ =
      weylFieldAction w σ (weylFieldAction w τ Φ) := by
  unfold weylFieldAction
  rw [mul_add, Real.exp_add]
  ring

def weylConnectionShift (B σ : ℝ) : ℝ := B - σ

theorem weylConnectionShift_compose (B σ τ : ℝ) :
    weylConnectionShift (weylConnectionShift B τ) σ =
      weylConnectionShift B (σ + τ) := by
  unfold weylConnectionShift
  ring

def complexifiedWeylScale (κ : ℂ) : ℂ := Complex.exp κ

theorem complexifiedWeylScale_add (κ₁ κ₂ : ℂ) :
    complexifiedWeylScale (κ₁ + κ₂) =
      complexifiedWeylScale κ₁ * complexifiedWeylScale κ₂ := by
  exact Complex.exp_add κ₁ κ₂

theorem complexifiedWeylScale_scaleLog (Ω : PositiveScale) :
    complexifiedWeylScale (scaleLog Ω : ℂ) = (Ω.1 : ℂ) := by
  change Complex.exp (↑(Real.log Ω.1)) = (Ω.1 : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_log Ω.2]

theorem complexifiedWeylScale_neg (κ : ℂ) :
    complexifiedWeylScale (-κ) = (complexifiedWeylScale κ)⁻¹ := by
  unfold complexifiedWeylScale
  exact Complex.exp_neg κ

theorem complexifiedWeylScale_neg_mul (κ : ℂ) :
    complexifiedWeylScale (-κ) * complexifiedWeylScale κ = 1 := by
  rw [complexifiedWeylScale_neg]
  exact inv_mul_cancel₀ (Complex.exp_ne_zero κ)

end
end InfoGeometry.Projective.WeylLogScaleBridge
