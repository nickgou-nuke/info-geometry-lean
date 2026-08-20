import Mathlib
import InfoGeometry.Projective.MobiusGauge

noncomputable section

namespace InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge

open InfoGeometry.Projective

variable {K : Type*} [Field K]

/--
The affine formula for the unique projective transformation sending the ordered
triple `(z₁,z₂,z₃)` to `(0,1,∞)`.

The third value is represented by the vanishing of the denominator rather than
by an affine value in `K`.
-/
def crossRatio (z z₁ z₂ z₃ : K) : K :=
  ((z - z₁) * (z₂ - z₃)) / ((z - z₃) * (z₂ - z₁))

/-- The normalizing cross-ratio vanishes at the first marked point. -/
@[simp]
theorem crossRatio_eval_z1 (z₁ z₂ z₃ : K) :
    crossRatio z₁ z₁ z₂ z₃ = 0 := by
  simp [crossRatio]

/-- The normalizing cross-ratio equals one at the second marked point. -/
theorem crossRatio_eval_z2
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₂₃ : z₂ ≠ z₃) :
    crossRatio z₂ z₁ z₂ z₃ = 1 := by
  unfold crossRatio
  have h₂₁ : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have h₂₃' : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h₂₃
  field_simp [h₂₁, h₂₃'] <;> ring

/-- The denominator of the normalizing cross-ratio vanishes at the third point. -/
@[simp]
theorem crossRatio_denominator_eval_z3 (z₁ z₂ z₃ : K) :
    (z₃ - z₃) * (z₂ - z₁) = 0 := by
  ring

/--
A genuine Möbius representative of the normalization
`(z₁,z₂,z₃) ↦ (0,1,∞)`.
-/
def threePointNormalizer
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) : MobiusMap K where
  α := z₂ - z₃
  β := -z₁ * (z₂ - z₃)
  γ := z₂ - z₁
  δ := -z₃ * (z₂ - z₁)
  det_ne_zero := by
    change
      (z₂ - z₃) * (-z₃ * (z₂ - z₁)) -
          (-z₁ * (z₂ - z₃)) * (z₂ - z₁) ≠ 0
    rw [show
      (z₂ - z₃) * (-z₃ * (z₂ - z₁)) -
          (-z₁ * (z₂ - z₃)) * (z₂ - z₁) =
        (z₂ - z₃) * (z₂ - z₁) * (z₁ - z₃) by ring]
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr h₂₃) (sub_ne_zero.mpr h₁₂.symm))
      (sub_ne_zero.mpr h₁₃)

/-- The numerator of the normalizer vanishes at `z₁`. -/
theorem threePointNormalizer_numerator_z1
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃).α * z₁ +
        (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃).β = 0 := by
  dsimp [threePointNormalizer]
  ring

/-- At `z₂`, the numerator and denominator of the normalizer agree. -/
theorem threePointNormalizer_numerator_eq_denominator_z2
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃).α * z₂ +
        (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃).β =
      (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃).γ * z₂ +
        (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃).δ := by
  dsimp [threePointNormalizer]
  ring

/-- The denominator of the normalizer vanishes at `z₃`. -/
theorem threePointNormalizer_denominator_z3
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    leftGauge (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃) z₃ = 0 := by
  dsimp [leftGauge, threePointNormalizer]
  ring

/-- The normalizer maps `z₁` to zero. -/
theorem threePointNormalizer_action_z1
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    projectiveAction (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃) z₁ = 0 := by
  unfold projectiveAction
  rw [threePointNormalizer_numerator_z1 z₁ z₂ z₃ h₁₂ h₁₃ h₂₃]
  simp

/-- The normalizer maps `z₂` to one. -/
theorem threePointNormalizer_action_z2
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    projectiveAction (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃) z₂ = 1 := by
  unfold projectiveAction
  rw [threePointNormalizer_numerator_eq_denominator_z2 z₁ z₂ z₃ h₁₂ h₁₃ h₂₃]
  apply div_self
  dsimp [threePointNormalizer]
  rw [show
    (z₂ - z₁) * z₂ + -z₃ * (z₂ - z₁) =
      (z₂ - z₁) * (z₂ - z₃) by ring]
  exact mul_ne_zero (sub_ne_zero.mpr h₁₂.symm) (sub_ne_zero.mpr h₂₃)

/-- The affine action of the normalizer is exactly the displayed cross-ratio. -/
theorem threePointNormalizer_action_eq_crossRatio
    (z z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    projectiveAction (threePointNormalizer z₁ z₂ z₃ h₁₂ h₁₃ h₂₃) z =
      crossRatio z z₁ z₂ z₃ := by
  unfold projectiveAction crossRatio
  dsimp [threePointNormalizer]
  congr 1
  · ring
  · ring

/--
The three projective normalization equations.  The third point is encoded by a
zero denominator, so this predicate does not confuse the affine carrier `K`
with its projective point at infinity.
-/
structure NormalizesTriple
    (T : MobiusMap K) (z₁ z₂ z₃ : K) : Prop where
  firstNumerator : T.α * z₁ + T.β = 0
  secondNumerator_eq_denominator : T.α * z₂ + T.β = T.γ * z₂ + T.δ
  thirdDenominator : T.γ * z₃ + T.δ = 0

/--
Projective uniqueness: every Möbius representative satisfying the three
normalization equations is a nonzero scalar multiple of the canonical
representative.
-/
theorem threePointNormalizer_projective_unique
    (T : MobiusMap K)
    (z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (hT : NormalizesTriple T z₁ z₂ z₃) :
    ∃ k : K, k ≠ 0 ∧
      T.α = k * (z₂ - z₃) ∧
      T.β = k * (-z₁ * (z₂ - z₃)) ∧
      T.γ = k * (z₂ - z₁) ∧
      T.δ = k * (-z₃ * (z₂ - z₁)) := by
  have hβ : T.β = -T.α * z₁ := by
    calc
      T.β = (T.α * z₁ + T.β) - T.α * z₁ := by ring
      _ = 0 - T.α * z₁ := by rw [hT.firstNumerator]
      _ = -T.α * z₁ := by ring
  have hδ : T.δ = -T.γ * z₃ := by
    calc
      T.δ = (T.γ * z₃ + T.δ) - T.γ * z₃ := by ring
      _ = 0 - T.γ * z₃ := by rw [hT.thirdDenominator]
      _ = -T.γ * z₃ := by ring
  have hrel : T.α * (z₂ - z₁) = T.γ * (z₂ - z₃) := by
    calc
      T.α * (z₂ - z₁) = T.α * z₂ + (-T.α * z₁) := by ring
      _ = T.α * z₂ + T.β := by rw [← hβ]
      _ = T.γ * z₂ + T.δ := hT.secondNumerator_eq_denominator
      _ = T.γ * z₂ + (-T.γ * z₃) := by rw [hδ]
      _ = T.γ * (z₂ - z₃) := by ring
  let k : K := T.γ / (z₂ - z₁)
  have h₂₁ : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have hγ : T.γ = k * (z₂ - z₁) := by
    simpa [k] using (div_mul_cancel₀ T.γ h₂₁).symm
  have hα : T.α = k * (z₂ - z₃) := by
    dsimp [k]
    field_simp [h₂₁]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrel
  have hβk : T.β = k * (-z₁ * (z₂ - z₃)) := by
    rw [hβ, hα]
    ring
  have hδk : T.δ = k * (-z₃ * (z₂ - z₁)) := by
    rw [hδ, hγ]
    ring
  have hk : k ≠ 0 := by
    intro hk0
    have hα0 : T.α = 0 := by rw [hα, hk0, zero_mul]
    have hβ0 : T.β = 0 := by rw [hβk, hk0, zero_mul]
    have hγ0 : T.γ = 0 := by rw [hγ, hk0, zero_mul]
    have hδ0 : T.δ = 0 := by rw [hδk, hk0, zero_mul]
    exact T.det_ne_zero (by simp [hα0, hβ0, hγ0, hδ0])
  exact ⟨k, hk, hα, hβk, hγ, hδk⟩

/--
Action-level uniqueness follows from coefficient uniqueness and cancellation of
the common nonzero projective scalar.
-/
theorem projectiveAction_eq_crossRatio_of_normalizesTriple
    (T : MobiusMap K)
    (z z₁ z₂ z₃ : K)
    (h₁₂ : z₁ ≠ z₂)
    (hT : NormalizesTriple T z₁ z₂ z₃) :
    projectiveAction T z = crossRatio z z₁ z₂ z₃ := by
  rcases threePointNormalizer_projective_unique
      T z₁ z₂ z₃ h₁₂ hT with
    ⟨k, hk, hα, hβ, hγ, hδ⟩
  unfold projectiveAction crossRatio
  rw [hα, hβ, hγ, hδ]
  rw [show
    k * (z₂ - z₃) * z + k * (-z₁ * (z₂ - z₃)) =
      k * ((z - z₁) * (z₂ - z₃)) by ring]
  rw [show
    k * (z₂ - z₁) * z + k * (-z₃ * (z₂ - z₁)) =
      k * ((z - z₃) * (z₂ - z₁)) by ring]
  exact mul_div_mul_left _ _ hk

/-- The original compatibility theorem, now over every field. -/
theorem master_three_point_moebius_cross_ratio_synthesis
    (z₁ z₂ z₃ : K) :
    crossRatio z₁ z₁ z₂ z₃ = 0 :=
  crossRatio_eval_z1 z₁ z₂ z₃

end InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge

end noncomputable section
