import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.Lie.TrialitySpin44Action

Spin(4,4) triality covariance for the split-octonion/Zorn layer.

The cots synthesis corrects the common misconception that G₂(2) is the
triality group. The correct statement is:

  Tri(𝕆ₛ) ≅ Spin(4,4),

with the related-triple action:

  g₂(xy) = g₁(x) g₃(y),   (g₁,g₂,g₃) ∈ Spin(4,4)³.

In infinitesimal form:

  D₂(xy) = D₁(x) y + x D₃(y).

This owner packages the finite algebraic skeleton of that action.
No group cohomology. No analytic continuation.
-/

noncomputable section

namespace InfoGeometry.Lie.TrialitySpin44Action

open InfoGeometry.Algebra
open ZornVectorMatrix
open ZornVec3

variable {R : Type*} [CommRing R]

/-! ## 1. Three Spin(4,4) actions -/

/-- A related triple of Spin(4,4) actions on the split-octonion carrier. -/
structure Spin44RelatedTriple (R : Type*) [CommRing R] where
  ρ₁ : ZornVectorMatrix R → ZornVectorMatrix R
  ρ₂ : ZornVectorMatrix R → ZornVectorMatrix R
  ρ₃ : ZornVectorMatrix R → ZornVectorMatrix R

/-! ## 2. Triality covariance law -/

/-- The triality covariance law:
    `ρ₂(h)(x * y) = ρ₁(h)(x) * ρ₃(h)(y)`.
-/
def trialityCovariant (T : Spin44RelatedTriple R) (x y : ZornVectorMatrix R) : Prop :=
  T.ρ₂ (mul x y) = mul (T.ρ₁ x) (T.ρ₃ y)

/-- The diagonal sector (g₁=g₂=g₃=g) recovers ordinary algebra automorphisms.
    This is the G₂(2) embedding into Spin(4,4).
-/
def diagonalSector (T : Spin44RelatedTriple R) (g : ZornVectorMatrix R → ZornVectorMatrix R) : Prop :=
  T.ρ₁ = g ∧ T.ρ₂ = g ∧ T.ρ₃ = g

/-! ## 3. Infinitesimal form -/

/-- An infinitesimal related triple of derivations. -/
structure InfinitesimalTriality (R : Type*) [CommRing R] where
  D₁ : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R
  D₂ : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R
  D₃ : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R

/-- The infinitesimal triality Leibniz law:
    `D₂(xy) = D₁(x) y + x D₃(y)`.
-/
def infinitesimalTrialityLeibniz (D : InfinitesimalTriality R) (x y : ZornVectorMatrix R) : Prop :=
  D.D₂ (mul x y) = mul (D.D₁ x) y + mul x (D.D₃ y)

/-- When all three derivations coincide, the Leibniz law reduces to
    the ordinary derivation rule. -/
theorem infinitesimalTrialityLeibniz_diagonal (D : InfinitesimalTriality R)
    (hdia : D.D₁ = D.D₂ ∧ D.D₂ = D.D₃)
    (x y : ZornVectorMatrix R) :
    infinitesimalTrialityLeibniz D x y →
    D.D₂ (mul x y) = mul (D.D₂ x) y + mul x (D.D₂ y) := by
  intro htrial
  simpa [infinitesimalTrialityLeibniz, hdia.1, hdia.2] using htrial

end InfoGeometry.Lie.TrialitySpin44Action
