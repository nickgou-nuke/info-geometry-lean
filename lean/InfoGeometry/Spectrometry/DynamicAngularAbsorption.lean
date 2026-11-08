import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.DynamicAngularAbsorption

noncomputable section

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
    (h₁ : 0 ≤ A * P12 * W) :
    internalRuler A P12 ε₁ ε₂ W =
      Real.sqrt (A * P12 * W) * Real.sqrt (ε₁ * ε₂) := by
  dsimp [internalRuler, coincidenceChannel]
  have h : A * P12 * ε₁ * ε₂ * W =
      (A * P12 * W) * (ε₁ * ε₂) := by ring
  rw [h]
  exact Real.sqrt_mul h₁ (ε₁ * ε₂)

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
  have hX' : internalRuler A P12 ε (ε * k) W ≠ 0 := by
    rw [mul_comm ε k]
    exact hX
  have hcancel : A * ε ≠ 0 := mul_ne_zero hA hε
  field_simp [hX', hP₂, hk, hcancel]

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
  let r := internalRuler A P12 ε₁ ε₂ W
  have hrSq : r ^ 2 = A * P12 * ε₁ * ε₂ * W := by
    dsimp [r, internalRuler, coincidenceChannel]
    exact Real.sq_sqrt hQ
  have hQne : A * P12 * ε₁ * ε₂ * W ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hP12) hε₁) hε₂) hW
  have hr : r ≠ 0 := by
    intro hz
    apply hQne
    have hzero : r ^ 2 = 0 := by simp [hz]
    rw [← hrSq, hzero]
  dsimp [productSlope, coefficient₁, coefficient₂, single₁, single₂]
  field_simp [hr, hP12, hW, hA, hε₁, hε₂]
  have hrSq' : (internalRuler A P12 ε₁ ε₂ W) ^ 2 =
      A * P12 * ε₁ * ε₂ * W := hrSq
  rw [hrSq']
  field_simp [hQne]

theorem activity_recovery_of_angular_normalization
    (H A P₁ P₂ P12 W : ℝ)
    (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hP12 : P12 ≠ 0) (hW : W ≠ 0)
    (hH : H = A * (P₁ * P₂) / (P12 * W)) :
    A = H * (P12 * W) / (P₁ * P₂) := by
  rw [hH]
  field_simp [hP₁, hP₂, hP12, hW]

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

end

end InfoGeometry.Spectrometry.DynamicAngularAbsorption
