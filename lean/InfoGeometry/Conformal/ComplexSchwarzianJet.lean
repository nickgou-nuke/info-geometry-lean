import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Complex Schwarzian calculus on certified derivative jets

The Schwarzian derivative depends only on the first three derivatives at one
point.  This file isolates that algebraic carrier over `ℂ` and proves the exact
composition law.  Analytic files may then supply derivative towers for concrete
functions without duplicating the rational Schwarzian algebra.

No stress tensor, central charge, projective structure, or physical state is
built into the definition.
-/

noncomputable section

namespace InfoGeometry.Conformal.ComplexSchwarzianJet

/-- Pre-Schwarzian coefficient attached to a first/second derivative pair. -/
def preSchwarzianJet (f₁ f₂ : ℂ) : ℂ :=
  f₂ / f₁

/-- Schwarzian coefficient attached to a noncritical third derivative jet. -/
def schwarzianJet (f₁ f₂ f₃ : ℂ) : ℂ :=
  f₃ / f₁ - (3 / 2 : ℂ) * (f₂ / f₁) ^ 2

/-- First derivative in the third-order chain rule for `g ∘ f`. -/
def compJet₁ (f₁ g₁ : ℂ) : ℂ :=
  g₁ * f₁

/-- Second derivative in the third-order chain rule for `g ∘ f`. -/
def compJet₂ (f₁ f₂ g₁ g₂ : ℂ) : ℂ :=
  g₂ * f₁ ^ 2 + g₁ * f₂

/-- Third derivative in the third-order chain rule for `g ∘ f`. -/
def compJet₃ (f₁ f₂ f₃ g₁ g₂ g₃ : ℂ) : ℂ :=
  g₃ * f₁ ^ 3 + 3 * g₂ * f₁ * f₂ + g₁ * f₃

/-- Exact pre-Schwarzian composition law. -/
theorem preSchwarzianJet_comp
    (f₁ f₂ g₁ g₂ : ℂ) (hf₁ : f₁ ≠ 0) (hg₁ : g₁ ≠ 0) :
    preSchwarzianJet (compJet₁ f₁ g₁) (compJet₂ f₁ f₂ g₁ g₂) =
      preSchwarzianJet g₁ g₂ * f₁ + preSchwarzianJet f₁ f₂ := by
  unfold preSchwarzianJet compJet₁ compJet₂
  have hcomp : g₁ * f₁ ≠ 0 := mul_ne_zero hg₁ hf₁
  field_simp [hf₁, hg₁, hcomp]

/-- Exact Schwarzian chain rule
`S(g ∘ f) = (S g ∘ f) (f')² + S f` at the level of derivative jets. -/
theorem schwarzianJet_comp
    (f₁ f₂ f₃ g₁ g₂ g₃ : ℂ)
    (hf₁ : f₁ ≠ 0) (hg₁ : g₁ ≠ 0) :
    schwarzianJet
        (compJet₁ f₁ g₁)
        (compJet₂ f₁ f₂ g₁ g₂)
        (compJet₃ f₁ f₂ f₃ g₁ g₂ g₃) =
      schwarzianJet g₁ g₂ g₃ * f₁ ^ 2 +
        schwarzianJet f₁ f₂ f₃ := by
  unfold schwarzianJet compJet₁ compJet₂ compJet₃
  have hcomp : g₁ * f₁ ≠ 0 := mul_ne_zero hg₁ hf₁
  field_simp [hf₁, hg₁, hcomp]
  ring

/-- The derivative jet of a fractional-linear map has zero Schwarzian.  Here
`Δ` is its determinant and `u` is its nonzero affine denominator. -/
theorem fractionalLinearJet_schwarzian_zero
    (u c Δ : ℂ) (hu : u ≠ 0) (hΔ : Δ ≠ 0) :
    schwarzianJet
        (Δ / u ^ 2)
        ((-2 * c * Δ) / u ^ 3)
        ((6 * c ^ 2 * Δ) / u ^ 4) = 0 := by
  unfold schwarzianJet
  field_simp [hu, hΔ]
  ring

/-- The logarithm jet has Schwarzian `1/(2z²)`.  This is an algebraic jet
identity; an analytic use must separately provide a local logarithm branch. -/
theorem logarithmJet_schwarzian
    (z : ℂ) (hz : z ≠ 0) :
    schwarzianJet (1 / z) (-1 / z ^ 2) (2 / z ^ 3) =
      1 / (2 * z ^ 2) := by
  unfold schwarzianJet
  field_simp [hz]
  ring

/-- Postcomposition by a zero-Schwarzian jet leaves the inner Schwarzian
unchanged.  This is the exact projective invariance statement at jet level. -/
theorem schwarzianJet_postcompose_zero
    (f₁ f₂ f₃ g₁ g₂ g₃ : ℂ)
    (hf₁ : f₁ ≠ 0) (hg₁ : g₁ ≠ 0)
    (hg : schwarzianJet g₁ g₂ g₃ = 0) :
    schwarzianJet
        (compJet₁ f₁ g₁)
        (compJet₂ f₁ f₂ g₁ g₂)
        (compJet₃ f₁ f₂ f₃ g₁ g₂ g₃) =
      schwarzianJet f₁ f₂ f₃ := by
  rw [schwarzianJet_comp f₁ f₂ f₃ g₁ g₂ g₃ hf₁ hg₁, hg]
  simp

end InfoGeometry.Conformal.ComplexSchwarzianJet
