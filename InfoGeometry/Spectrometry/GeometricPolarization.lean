import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.GeometricPolarization

open Real

section Factorization

def polarizationFactor (W W₀ : ℝ) : ℝ := W / W₀

theorem polarization_identity (W W₀ : ℝ) (hW₀ : W₀ ≠ 0) :
    polarizationFactor W W₀ * W₀ = W := by
  dsimp [polarizationFactor]
  exact div_mul_cancel₀ W hW₀

end Factorization

section Ruler

def polarizedCoincidence
    (A P12 ε₁ ε₂ ω W₀ : ℝ) : ℝ :=
  A * P12 * ε₁ * ε₂ * (ω * W₀)

noncomputable def nuclearCore (A P12 W₀ : ℝ) : ℝ :=
  Real.sqrt (A * P12 * W₀)

noncomputable def polarizedTransport (ε₁ ε₂ ω : ℝ) : ℝ :=
  Real.sqrt (ε₁ * ε₂ * ω)

theorem ruler_decoupling
    (A P12 ε₁ ε₂ ω W₀ : ℝ)
    (hN : 0 ≤ A * P12 * W₀)
    (hT : 0 ≤ ε₁ * ε₂ * ω) :
    Real.sqrt (polarizedCoincidence A P12 ε₁ ε₂ ω W₀) =
      nuclearCore A P12 W₀ * polarizedTransport ε₁ ε₂ ω := by
  dsimp [polarizedCoincidence, nuclearCore, polarizedTransport]
  have h : A * P12 * ε₁ * ε₂ * (ω * W₀) =
      (A * P12 * W₀) * (ε₁ * ε₂ * ω) := by ring
  rw [h]
  exact Real.sqrt_mul hN

end Ruler

section PointwiseSlope

def pointwiseSlope
    (A P₁ P₂ P12 ε₁ ε₂ ω W₀ : ℝ) : ℝ :=
  (A * P₁ * ε₁) * (A * P₂ * ε₂) /
    polarizedCoincidence A P12 ε₁ ε₂ ω W₀

theorem pointwise_slope_modulation
    (A P₁ P₂ P12 ε₁ ε₂ ω W₀ : ℝ)
    (hA : A ≠ 0) (hP12 : P12 ≠ 0) (hW₀ : W₀ ≠ 0)
    (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hω : ω ≠ 0) :
    pointwiseSlope A P₁ P₂ P12 ε₁ ε₂ ω W₀ =
      (A * (P₁ * P₂) / (P12 * W₀)) * (1 / ω) := by
  dsimp [pointwiseSlope, polarizedCoincidence]
  have h₁ : A * ε₁ * ε₂ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hA hε₁) hε₂
  have h₂ : P12 * W₀ * ω ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hP12 hW₀) hω
  field_simp [h₁, h₂]
  ring

end PointwiseSlope

section AsymptoticReference

theorem reference_factor_unwinds_at_one
    (A P₁ P₂ P12 W₀ : ℝ) :
    (A * (P₁ * P₂) / (P12 * W₀)) * (1 / (1 : ℝ)) =
      A * (P₁ * P₂) / (P12 * W₀) := by
  ring

theorem activity_recovery_from_reference_slope
    (H A P₁ P₂ P12 W₀ : ℝ)
    (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hP12 : P12 ≠ 0) (hW₀ : W₀ ≠ 0)
    (hH : H = A * (P₁ * P₂) / (P12 * W₀)) :
    A = H * (P12 * W₀) / (P₁ * P₂) := by
  rw [hH]
  field_simp [hP₁, hP₂, hP12, hW₀]
  ring

end AsymptoticReference

section CausalOrder

def causal (a b : ℕ) : Prop := a ≤ b

theorem archetype_chain :
    causal 210 211 ∧ causal 211 212 ∧ causal 212 213 := by
  norm_num [causal]

theorem causal_refl (a : ℕ) : causal a a := le_rfl

theorem causal_trans {a b c : ℕ} : causal a b → causal b c → causal a c :=
  le_trans

theorem causal_antisymm {a b : ℕ} : causal a b → causal b a → a = b :=
  le_antisymm

end CausalOrder

end InfoGeometry.Spectrometry.GeometricPolarization
