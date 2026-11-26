/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

variable {R : Type*} [Ring R]

/-! ## 1. Three Spin(4,4) actions -/

/-- A related triple of Spin(4,4) actions on the split-octonion carrier. -/
structure Spin44RelatedTriple (R : Type*) [Ring R] where
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
structure InfinitesimalTriality (R : Type*) [Ring R] where
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

/-- The diagonal triality sector `(g, g, g)` is identically the automorphism sector of `mul`. -/
theorem automorphismGroup_is_diagonal_sector
    (g : ZornVectorMatrix R → ZornVectorMatrix R) :
    (∀ X Y, trialityCovariant ⟨g, g, g⟩ X Y) ↔
      (∀ X Y, g (mul X Y) = mul (g X) (g Y)) :=
  Iff.rfl

/-- Any endomorphism intertwining right-multiplication by `one` with left-multiplication and
sending `one` to `scalar a` acts as right multiplication by `scalar a` (hence left scalar
multiplication over a commutative ring). -/
theorem commutant_left_multiplication_scalar {R : Type*} [CommRing R]
    (L : ZornVectorMatrix R → (ZornVectorMatrix R → ZornVectorMatrix R))
    (hL : ∀ x, L x = mul x)
    (T : ZornVectorMatrix R → ZornVectorMatrix R)
    (hcomm : ∀ x, T (mul x one) = L x (T one))
    (hUnit : ∃ a : R, T one = scalar a) :
    ∃ a : R, T = (fun z => mul (scalar a) z) := by
  rcases hUnit with ⟨a, ha⟩
  refine ⟨a, funext fun z => ?_⟩
  have hz := hcomm z
  rw [ZornVectorMatrix.mul_one, hL z, ha] at hz
  rw [hz]
  ext i <;> simp [mul, scalar, ZornVec3.dot, ZornVec3.cross, mul_comm]

/-- Any two purely imaginary split-octonion elements satisfying split-signature orthogonality
`dot eᵢ.v eⱼ.w + dot eⱼ.v eᵢ.w = 0` satisfy the Clifford anticommutation relation
`mul eᵢ eⱼ + mul eⱼ eᵢ = zero`. -/
theorem leftMultiplication_clifford_relation {R : Type*} [CommRing R]
    (e_i e_j : ZornVectorMatrix R)
    (himag : e_i.a = 0 ∧ e_i.b = 0 ∧ e_j.a = 0 ∧ e_j.b = 0)
    (horth : dot e_i.v e_j.w + dot e_j.v e_i.w = 0) :
    mul e_i e_j + mul e_j e_i = zero := by
  rcases himag with ⟨hia, hib, hja, hjb⟩
  have horth' :
      dot e_i.w e_j.v + dot e_j.w e_i.v = 0 := by
    have hc1 : dot e_i.w e_j.v = dot e_j.v e_i.w := by
      simp [dot, Fin.sum_univ_three]; ring
    have hc2 : dot e_j.w e_i.v = dot e_i.v e_j.w := by
      simp [dot, Fin.sum_univ_three]; ring
    rw [hc1, hc2, _root_.add_comm]
    exact horth
  ext k
  · simp [mul, hia, hja, zero, horth]
  · fin_cases k <;> simp [mul, hia, hib, hja, hjb, cross, zero] <;> ring
  · fin_cases k <;> simp [mul, hia, hib, hja, hjb, cross, zero] <;> ring
  · simp [mul, hib, hjb, zero, horth']

end InfoGeometry.Lie.TrialitySpin44Action
