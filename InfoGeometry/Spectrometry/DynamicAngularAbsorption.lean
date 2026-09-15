import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.DynamicAngularAbsorption

open Real

/-!
The square-root coincidence coordinate internalizes the measured angular factor
for relative transport.  Absolute activity extraction still requires an angular
normalization, which is stated explicitly below.
-/

section Coordinate

def coincidenceChannel (A P12 ε₁ ε₂ W : ℝ) : ℝ :=
  A * P12 * ε₁ * ε₂ * W

noncomputable def internalRuler (A P12 ε₁ ε₂ W : ℝ) : ℝ :=
  Real.sqrt (coincidenceChannel A P12 ε₁ ε₂ W)

theorem ruler_factorization
    (A P12 ε₁ ε₂ W : ℝ)
    (h₁ : 0 ≤ A * P12 * W) (h₂ : 0 ≤ ε₁ * ε₂) :
    internalRuler A P12 ε₁ ε₂ W =
      Real.sqrt (A * P12 * W) * Real.sqrt (ε₁ * ε₂) := by
  dsimp [internalRuler, coincidenceChannel]
  have h : A * P12 * ε₁ * ε₂ * W =
      (A * P12 * W) * (ε₁ * ε₂) := by ring
  rw [h]
  exact Real.sqrt_mul h₁

end Coordinate

section RelativeTransport

def single₁ (A P₁ ε₁ : ℝ) : ℝ := A * P₁ * ε₁
def single₂ (A P₂ ε₂ : ℝ) : ℝ := A * P₂ * ε₂

noncomputable def coefficient₁
    (A P₁ P12 ε₁ ε₂ W : ℝ) : ℝ :=
  single₁ A P₁ ε₁ / internalRuler A P12 ε₁ ε₂ W

noncomputable def coefficient₂
    (A P₂ P12 ε₁ ε₂ W : ℝ) : ℝ :=
  single₂ A P₂ ε₂ / internalRuler A P12 ε₁ ε₂ W

theorem coefficient_ratio
    (A P₁ P₂ P12 ε k W : ℝ)
    (hA : A ≠ 0) (hP₂ : P₂ ≠ 0) (hk : k ≠ 0)
    (hε : ε ≠ 0)
    (hX : internalRuler A P12 ε (k * ε) W ≠ 0) :
    coefficient₁ A P₁ P12 ε (k * ε) W /
        coefficient₂ A P₂ P12 ε (k * ε) W = P₁ / (k * P₂) := by
  dsimp [coefficient₁, coefficient₂, single₁, single₂]
  have hcancel : A * ε ≠ 0 := mul_ne_zero hA hε
  field_simp [hX, hP₂, hk, hcancel]
  ring

end RelativeTransport

section ProductSlope

noncomputable def productSlope
    (A P₁ P₂ P12 ε₁ ε₂ W : ℝ) : ℝ :=
  coefficient₁ A P₁ P12 ε₁ ε₂ W *
    coefficient₂ A P₂ P12 ε₁ ε₂ W

theorem product_slope_efficiency_cancellation
    (A P₁ P₂ P12 ε₁ ε₂ W : ℝ)
    (hQ : 0 ≤ coincidenceChannel A P12 ε₁ ε₂ W)
    (hA : A ≠ 0) (hP12 : P12 ≠ 0)
    (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hW : W ≠ 0) :
    productSlope A P₁ P₂ P12 ε₁ ε₂ W =
      A * (P₁ * P₂) / (P12 * W) := by
  dsimp [productSlope, coefficient₁, coefficient₂, single₁, single₂,
    internalRuler, coincidenceChannel]
  have hQne : A * P12 * ε₁ * ε₂ * W ≠ 0 := by
    repeat' apply mul_ne_zero
    exact hA
    exact hP12
    exact hε₁
    exact hε₂
    exact hW
  have hsqrt : Real.sqrt (A * P12 * ε₁ * ε₂ * W) ^ 2 =
      A * P12 * ε₁ * ε₂ * W := Real.sq_sqrt hQ
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
  field_simp [hQne, hsqrt]
  ring

theorem activity_recovery_of_angular_normalization
    (H A P₁ P₂ P12 W : ℝ)
    (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hP12 : P12 ≠ 0) (hW : W ≠ 0)
    (hH : H = A * (P₁ * P₂) / (P12 * W)) :
    A = H * (P12 * W) / (P₁ * P₂) := by
  rw [hH]
  field_simp [hP₁, hP₂, hP12, hW]
  ring

theorem activity_recovery_at_reference_factor
    (H A P₁ P₂ P12 W₀ : ℝ)
    (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hP12 : P12 ≠ 0) (hW₀ : W₀ ≠ 0)
    (hH : H = A * (P₁ * P₂) / (P12 * W₀)) :
    A = H * P12 * W₀ / (P₁ * P₂) := by
  have h := activity_recovery_of_angular_normalization
    H A P₁ P₂ P12 W₀ hP₁ hP₂ hP12 hW₀ hH
  simpa [mul_assoc] using h

end ProductSlope

section CausalOrder

def causal (a b : ℕ) : Prop := a ≤ b

theorem archetype_chain :
    causal 205 206 ∧ causal 206 207 ∧ causal 207 208 := by
  norm_num [causal]

theorem causal_refl (a : ℕ) : causal a a := by
  exact le_rfl

theorem causal_trans {a b c : ℕ} : causal a b → causal b c → causal a c := by
  exact le_trans

theorem causal_antisymm {a b : ℕ} : causal a b → causal b a → a = b := by
  exact le_antisymm

end CausalOrder

end InfoGeometry.Spectrometry.DynamicAngularAbsorption
