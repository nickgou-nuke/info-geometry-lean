import Mathlib.Tactic
import InfoGeometry.Canonical.HestenesKreinItakuraSaitoColimit

/-!
# Real rapidity coordinates for the projective ratio

The real-positive chart admits a native rapidity parameter without invoking a
complex branch of `log` or `artanh`.  We define the centered velocity by its
exponential coordinate and prove that its projective ratio is `exp (2 * χ)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinRapidityCrossRatio

open InfoGeometry.Canonical.HestenesKreinItakuraSaitoColimit

def rapidityRatio (χ : ℝ) : ℝ := Real.exp (2 * χ)

def centeredVelocity (χ : ℝ) : ℝ :=
  (rapidityRatio χ - 1) / (rapidityRatio χ + 1)

def centeredVelocityRapidity (v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 + v) / (1 - v))

theorem rapidityRatio_pos (χ : ℝ) : 0 < rapidityRatio χ := by
  unfold rapidityRatio
  exact Real.exp_pos _

theorem rapidityRatio_neg (χ : ℝ) :
    rapidityRatio (-χ) = (rapidityRatio χ)⁻¹ := by
  unfold rapidityRatio
  rw [show 2 * -χ = -(2 * χ) by ring, Real.exp_neg]

theorem rapidityRatio_injective : Function.Injective rapidityRatio := by
  intro χ₁ χ₂ h
  have hlog : 2 * χ₁ = 2 * χ₂ := Real.exp_injective h
  linarith

theorem rapidityRatio_add (χ ψ : ℝ) :
    rapidityRatio (χ + ψ) = rapidityRatio χ * rapidityRatio ψ := by
  unfold rapidityRatio
  rw [mul_add, Real.exp_add]

theorem centeredVelocity_neg (χ : ℝ) :
    centeredVelocity (-χ) = -centeredVelocity χ := by
  unfold centeredVelocity
  rw [rapidityRatio_neg]
  have hpos : 0 < rapidityRatio χ := rapidityRatio_pos χ
  have hne : rapidityRatio χ ≠ 0 := ne_of_gt hpos
  have hden : rapidityRatio χ + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hne, hden]
  ring

theorem centeredVelocity_add (χ ψ : ℝ) :
    centeredVelocity (χ + ψ) =
      (centeredVelocity χ + centeredVelocity ψ) /
        (1 + centeredVelocity χ * centeredVelocity ψ) := by
  unfold centeredVelocity
  rw [rapidityRatio_add]
  have hχ : 0 < rapidityRatio χ := rapidityRatio_pos χ
  have hψ : 0 < rapidityRatio ψ := rapidityRatio_pos ψ
  have hχ' : rapidityRatio χ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hψ' : rapidityRatio ψ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hden :
      0 < 1 +
        ((rapidityRatio χ - 1) / (rapidityRatio χ + 1)) *
          ((rapidityRatio ψ - 1) / (rapidityRatio ψ + 1)) := by
    have hrewrite :
        1 +
            ((rapidityRatio χ - 1) / (rapidityRatio χ + 1)) *
              ((rapidityRatio ψ - 1) / (rapidityRatio ψ + 1)) =
          (2 * (rapidityRatio χ * rapidityRatio ψ + 1)) /
            ((rapidityRatio χ + 1) * (rapidityRatio ψ + 1)) := by
      field_simp [hχ', hψ']
      ring
    rw [hrewrite]
    positivity
  have hleft : 0 < rapidityRatio χ * rapidityRatio ψ + 1 := by
    positivity
  apply (div_eq_div_iff (ne_of_gt hleft) (ne_of_gt hden)).2
  field_simp [hχ', hψ']
  ring

theorem centeredVelocity_mem_Ioo (χ : ℝ) :
    centeredVelocity χ ∈ Set.Ioo (-1 : ℝ) 1 := by
  unfold centeredVelocity
  have hpos : 0 < rapidityRatio χ := rapidityRatio_pos χ
  have hden : 0 < rapidityRatio χ + 1 := by linarith
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_iff₀ hden).2
    linarith

theorem realCrossRatio_centeredVelocity (χ : ℝ) :
    realCrossRatio ((1 + centeredVelocity χ) / 2) = rapidityRatio χ := by
  unfold realCrossRatio centeredVelocity
  have hpos : 0 < rapidityRatio χ := rapidityRatio_pos χ
  have hden : rapidityRatio χ + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hden]
  ring

theorem realCrossRatio_centeredVelocity_exp (χ : ℝ) :
    realCrossRatio ((1 + centeredVelocity χ) / 2) = Real.exp (2 * χ) := by
  exact realCrossRatio_centeredVelocity χ

theorem realCrossRatio_centeredVelocity_neg (χ : ℝ) :
    realCrossRatio ((1 + centeredVelocity (-χ)) / 2) =
      (realCrossRatio ((1 + centeredVelocity χ) / 2))⁻¹ := by
  rw [realCrossRatio_centeredVelocity, realCrossRatio_centeredVelocity,
    rapidityRatio_neg]

theorem centeredVelocity_injective : Function.Injective centeredVelocity := by
  intro χ₁ χ₂ h
  apply rapidityRatio_injective
  have hcross := congrArg
    (fun v : ℝ => realCrossRatio ((1 + v) / 2)) h
  simpa only [realCrossRatio_centeredVelocity] using hcross

theorem centeredVelocityRapidity_centeredVelocity (χ : ℝ) :
    centeredVelocityRapidity (centeredVelocity χ) = χ := by
  unfold centeredVelocityRapidity
  have hpos : 0 < rapidityRatio χ := rapidityRatio_pos χ
  have hden : rapidityRatio χ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hratio :
      (1 + centeredVelocity χ) / (1 - centeredVelocity χ) =
        rapidityRatio χ := by
    unfold centeredVelocity
    field_simp [hden]
    ring
  rw [hratio]
  unfold rapidityRatio
  rw [Real.log_exp]
  change (1 / 2 : ℝ) * (2 * χ) = χ
  ring

theorem rapidityRatio_centeredVelocityRapidity {v : ℝ}
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    rapidityRatio (centeredVelocityRapidity v) =
      (1 + v) / (1 - v) := by
  rcases hv with ⟨hlo, hhi⟩
  have hminus : 0 < 1 - v := by linarith
  have hplus : 0 < 1 + v := by linarith
  have hratio : 0 < (1 + v) / (1 - v) := div_pos hplus hminus
  unfold rapidityRatio centeredVelocityRapidity
  rw [show 2 * ((1 / 2 : ℝ) * Real.log ((1 + v) / (1 - v))) =
      Real.log ((1 + v) / (1 - v)) by ring]
  exact Real.exp_log hratio

theorem centeredVelocityRapidity_neg {v : ℝ}
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    centeredVelocityRapidity (-v) =
      -centeredVelocityRapidity v := by
  rcases hv with ⟨hlo, hhi⟩
  have hminus : 1 - v ≠ 0 := by linarith
  have hplus : 1 + v ≠ 0 := by linarith
  have hratio :
      (1 + -v) / (1 - -v) = ((1 + v) / (1 - v))⁻¹ := by
    field_simp [hminus, hplus]
    ring
  unfold centeredVelocityRapidity
  rw [hratio, Real.log_inv]
  ring

/- The logarithmic rapidity chart is a left inverse on the physical interval. -/
theorem centeredVelocity_centeredVelocityRapidity {v : ℝ}
    (hv : v ∈ Set.Ioo (-1) 1) :
    centeredVelocity (centeredVelocityRapidity v) = v := by
  rcases hv with ⟨hlo, hhi⟩
  have hminus : 0 < 1 - v := by linarith
  have hplus : 0 < 1 + v := by linarith
  have hratio : 0 < (1 + v) / (1 - v) := div_pos hplus hminus
  unfold centeredVelocity centeredVelocityRapidity rapidityRatio
  have hexp :
      Real.exp (2 * ((1 / 2 : ℝ) * Real.log ((1 + v) / (1 - v)))) =
        (1 + v) / (1 - v) := by
    rw [show 2 * ((1 / 2 : ℝ) * Real.log ((1 + v) / (1 - v))) =
        Real.log ((1 + v) / (1 - v)) by ring]
    exact Real.exp_log hratio
  rw [hexp]
  field_simp [ne_of_gt hminus]
  ring

theorem rapidity_crossRatio_is_modularTomita (χ : ℝ) :
    itakuraSaitoDeviance
        (realCrossRatio ((1 + centeredVelocity χ) / 2)) =
      modularTomitaDeviance (2 * χ) := by
  rw [realCrossRatio_centeredVelocity_exp]
  exact itakuraSaitoDeviance_exp _

theorem rapidity_crossRatio_is_nonneg (χ : ℝ) :
    0 ≤ itakuraSaitoDeviance
        (realCrossRatio ((1 + centeredVelocity χ) / 2)) := by
  rw [rapidity_crossRatio_is_modularTomita]
  exact modularTomitaDeviance_nonneg _

theorem centeredVelocity_zero : centeredVelocity 0 = 0 := by
  norm_num [centeredVelocity, rapidityRatio]

theorem rapidity_seam_zero :
    itakuraSaitoDeviance
        (realCrossRatio ((1 + centeredVelocity 0) / 2)) = 0 := by
  rw [centeredVelocity_zero]
  norm_num [realCrossRatio, itakuraSaitoDeviance]

theorem centeredVelocity_eq_zero_iff {χ : ℝ} :
    centeredVelocity χ = 0 ↔ χ = 0 := by
  constructor
  · intro h
    apply centeredVelocity_injective
    simpa [centeredVelocity_zero] using h
  · intro h
    simpa [h] using centeredVelocity_zero

theorem centeredVelocityRapidity_eq_half_log_realCrossRatio {v : ℝ}
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    centeredVelocityRapidity v =
      (1 / 2 : ℝ) * Real.log (realCrossRatio ((1 + v) / 2)) := by
  rcases hv with ⟨hlo, hhi⟩
  have hminus : 1 - v ≠ 0 := by linarith
  have hhalf : 1 - (1 + v) / 2 = (1 - v) / 2 := by ring
  unfold centeredVelocityRapidity realCrossRatio
  congr 2
  rw [hhalf]
  field_simp [hminus]

theorem centeredVelocity_range :
    Set.range centeredVelocity = Set.Ioo (-1 : ℝ) 1 := by
  ext v
  constructor
  · rintro ⟨χ, rfl⟩
    exact centeredVelocity_mem_Ioo χ
  · intro hv
    exact ⟨centeredVelocityRapidity v, centeredVelocity_centeredVelocityRapidity hv⟩

noncomputable def centeredVelocityEquiv :
    ℝ ≃ Set.Ioo (-1 : ℝ) 1 where
  toFun χ := ⟨centeredVelocity χ, centeredVelocity_mem_Ioo χ⟩
  invFun v := centeredVelocityRapidity v.1
  left_inv χ := centeredVelocityRapidity_centeredVelocity χ
  right_inv v := Subtype.ext (centeredVelocity_centeredVelocityRapidity v.property)

end InfoGeometry.Canonical.HestenesKreinRapidityCrossRatio

end noncomputable section
