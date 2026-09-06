import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Typed boundary multipliers

This file supplies the smallest analytic carrier needed before introducing
Hardy-space or Fredholm structure.  A boundary multiplier is only a complex
symbol together with a pointwise unit-modulus law.  No measure, Hilbert-space,
trace-class, or index assertion is bundled here.
-/

noncomputable section

namespace InfoGeometry.Topology.BoundaryMultiplierCore

structure BoundaryMultiplierDatum where
  symbol : ℝ → ℂ
  norm_one : ∀ γ, ‖symbol γ‖ = 1

def phaseDatum (θ : ℝ → ℝ) : BoundaryMultiplierDatum where
  symbol := fun γ => ⟨Real.cos (θ γ), Real.sin (θ γ)⟩
  norm_one := by
    intro γ
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply]
    have htrig : Real.cos (θ γ) * Real.cos (θ γ) +
        Real.sin (θ γ) * Real.sin (θ γ) = 1 := by
      nlinarith [Real.cos_sq_add_sin_sq (θ γ)]
    rw [htrig]
    norm_num

@[simp] theorem phaseDatum_symbol_apply (θ : ℝ → ℝ) (γ : ℝ) :
    (phaseDatum θ).symbol γ =
      ⟨Real.cos (θ γ), Real.sin (θ γ)⟩ :=
  rfl

theorem phaseDatum_reflection (θ : ℝ → ℝ)
    (hθ : ∀ γ, θ (-γ) = -θ γ) (γ : ℝ) :
    (phaseDatum θ).symbol (-γ) =
      starRingEnd ℂ ((phaseDatum θ).symbol γ) := by
  apply Complex.ext
  · simp [hθ]
  · simp [hθ]

def one : BoundaryMultiplierDatum where
  symbol := fun _ => 1
  norm_one := by intro γ; simp

def product (B C : BoundaryMultiplierDatum) : BoundaryMultiplierDatum where
  symbol := fun γ => B.symbol γ * C.symbol γ
  norm_one := by
    intro γ
    rw [norm_mul, B.norm_one γ, C.norm_one γ, one_mul]

@[simp] theorem one_symbol_apply (γ : ℝ) :
    one.symbol γ = 1 :=
  rfl

@[simp] theorem product_symbol_apply (B C : BoundaryMultiplierDatum) (γ : ℝ) :
    (product B C).symbol γ = B.symbol γ * C.symbol γ :=
  rfl

theorem product_symbol_assoc (B C D : BoundaryMultiplierDatum) (γ : ℝ) :
    (product (product B C) D).symbol γ =
      (product B (product C D)).symbol γ := by
  simp [mul_assoc]

theorem product_symbol_comm (B C : BoundaryMultiplierDatum) (γ : ℝ) :
    (product B C).symbol γ = (product C B).symbol γ := by
  simp [mul_comm]

theorem phaseDatum_product_add_symbol (θ φ : ℝ → ℝ) (γ : ℝ) :
    (product (phaseDatum θ) (phaseDatum φ)).symbol γ =
      (phaseDatum (θ + φ)).symbol γ := by
  apply Complex.ext <;>
  simp [Real.cos_add, Real.sin_add, mul_add, add_mul]
  <;> ring

def conjugate (B : BoundaryMultiplierDatum) : BoundaryMultiplierDatum where
  symbol := fun γ => starRingEnd ℂ (B.symbol γ)
  norm_one := by
    intro γ
    simpa using B.norm_one γ

def multiply (B : BoundaryMultiplierDatum) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun γ => B.symbol γ * f γ

theorem multiply_product (B C : BoundaryMultiplierDatum) (f : ℝ → ℂ) :
    multiply (product B C) f = multiply B (multiply C f) := by
  funext γ
  simp [multiply, mul_assoc]

theorem multiply_one (f : ℝ → ℂ) :
    multiply one f = f := by
  funext γ
  simp [multiply]

def multiplyInv (B : BoundaryMultiplierDatum) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun γ => starRingEnd ℂ (B.symbol γ) * f γ

@[simp] theorem conjugate_symbol_apply (B : BoundaryMultiplierDatum) (γ : ℝ) :
    (conjugate B).symbol γ = starRingEnd ℂ (B.symbol γ) :=
  rfl

@[simp] theorem multiply_apply (B : BoundaryMultiplierDatum) (f : ℝ → ℂ)
    (γ : ℝ) :
    multiply B f γ = B.symbol γ * f γ :=
  rfl

theorem symbol_ne_zero (B : BoundaryMultiplierDatum) (γ : ℝ) :
    B.symbol γ ≠ 0 := by
  have hnorm := B.norm_one γ
  intro h
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

theorem norm_multiply_apply (B : BoundaryMultiplierDatum) (f : ℝ → ℂ)
    (γ : ℝ) :
    ‖multiply B f γ‖ = ‖f γ‖ := by
  rw [multiply_apply, norm_mul, B.norm_one, one_mul]

theorem multiply_preserves_zero (B : BoundaryMultiplierDatum) :
    multiply B (fun _ => 0) = fun _ => 0 := by
  funext γ
  simp [multiply]

@[simp] theorem multiplyInv_apply (B : BoundaryMultiplierDatum) (f : ℝ → ℂ)
    (γ : ℝ) :
    multiplyInv B f γ = starRingEnd ℂ (B.symbol γ) * f γ :=
  rfl

theorem multiplyInv_eq_conjugate_multiply (B : BoundaryMultiplierDatum)
    (f : ℝ → ℂ) :
    multiplyInv B f = multiply (conjugate B) f :=
  rfl

theorem symbol_conj_mul (B : BoundaryMultiplierDatum) (γ : ℝ) :
    starRingEnd ℂ (B.symbol γ) * B.symbol γ = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq, B.norm_one γ]
  norm_num

theorem symbol_mul_conj (B : BoundaryMultiplierDatum) (γ : ℝ) :
    B.symbol γ * starRingEnd ℂ (B.symbol γ) = 1 := by
  simpa [mul_comm] using symbol_conj_mul B γ

theorem product_conjugate_symbol_eq_one (B : BoundaryMultiplierDatum) (γ : ℝ) :
    (product (conjugate B) B).symbol γ = 1 := by
  simpa [product_symbol_apply] using symbol_conj_mul B γ

theorem product_conjugate_symbol_eq_one' (B : BoundaryMultiplierDatum) (γ : ℝ) :
    (product B (conjugate B)).symbol γ = 1 := by
  simpa [product_symbol_apply] using symbol_mul_conj B γ

theorem multiplyInv_left_inverse (B : BoundaryMultiplierDatum) (f : ℝ → ℂ) :
    multiplyInv B (multiply B f) = f := by
  funext γ
  rw [multiplyInv_apply, multiply_apply, ← mul_assoc, symbol_conj_mul,
    one_mul]

theorem multiplyInv_right_inverse (B : BoundaryMultiplierDatum) (f : ℝ → ℂ) :
    multiply B (multiplyInv B f) = f := by
  funext γ
  rw [multiply_apply, multiplyInv_apply, ← mul_assoc]
  rw [symbol_mul_conj, one_mul]

/-- Pointwise unit-modulus multiplication is an equivalence of function spaces. -/
def multiplyEquiv (B : BoundaryMultiplierDatum) : (ℝ → ℂ) ≃ (ℝ → ℂ) where
  toFun := multiply B
  invFun := multiplyInv B
  left_inv := multiplyInv_left_inverse B
  right_inv := multiplyInv_right_inverse B

theorem multiply_injective (B : BoundaryMultiplierDatum) :
    Function.Injective (multiply B) := by
  intro f g h
  funext γ
  apply (mul_left_cancel₀ (symbol_ne_zero B γ))
  exact congrFun h γ

end InfoGeometry.Topology.BoundaryMultiplierCore
