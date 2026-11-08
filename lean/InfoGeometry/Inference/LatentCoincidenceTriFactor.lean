import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Latent conditional tri-factor coincidence model

For a finite ordered coincidence table, the observation law is represented by
three finite factors

`L : I → A`, `S : A → B`, and `R : J → B`.

The observed coincidence intensity is the nonnegative mixture
`sum a, sum b, L i a * S a b * R j b`.  The middle factor is the latent
coupling; the outer factors are conditional observation profiles.  This file
does not assert uniqueness, statistical identifiability, or Sinkhorn
existence/convergence.
-/

namespace InfoGeometry.Inference.LatentCoincidenceTriFactor

variable {I J A B : Type*}
variable [Fintype A] [Fintype B]

def latentCoincidence
    (L : Matrix I A ℝ) (S : Matrix A B ℝ) (R : Matrix J B ℝ) :
    Matrix I J ℝ :=
  fun i j => ∑ a : A, ∑ b : B, (L i a * S a b) * R j b

@[simp] theorem latentCoincidence_apply
    (L : Matrix I A ℝ) (S : Matrix A B ℝ) (R : Matrix J B ℝ)
    (i : I) (j : J) :
    latentCoincidence L S R i j =
      ∑ a : A, ∑ b : B, (L i a * S a b) * R j b := rfl

theorem latentCoincidence_nonneg
    (L : Matrix I A ℝ) (S : Matrix A B ℝ) (R : Matrix J B ℝ)
    (hL : ∀ i a, 0 ≤ L i a)
    (hS : ∀ a b, 0 ≤ S a b)
    (hR : ∀ j b, 0 ≤ R j b) (i : I) (j : J) :
    0 ≤ latentCoincidence L S R i j := by
  unfold latentCoincidence
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (mul_nonneg (hL i a) (hS a b)) (hR j b)

def gaugeLeft (L : Matrix I A ℝ) (d : A → ℝ) : Matrix I A ℝ :=
  fun i a => L i a * d a

def gaugeRight (R : Matrix J B ℝ) (e : B → ℝ) : Matrix J B ℝ :=
  fun j b => R j b * e b

noncomputable def gaugeMiddle (S : Matrix A B ℝ) (d : A → ℝ) (e : B → ℝ) : Matrix A B ℝ :=
  fun a b => (d a)⁻¹ * S a b * (e b)⁻¹

theorem latentCoincidence_gauge_invariant
    (L : Matrix I A ℝ) (S : Matrix A B ℝ) (R : Matrix J B ℝ)
    (d : A → ℝ) (e : B → ℝ)
    (hd : ∀ a, d a ≠ 0) (he : ∀ b, e b ≠ 0) :
    latentCoincidence (gaugeLeft L d) (gaugeMiddle S d e) (gaugeRight R e) =
      latentCoincidence L S R := by
  funext i j
  unfold latentCoincidence gaugeLeft gaugeMiddle gaugeRight
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  field_simp [hd a, he b]

theorem latentCoincidence_eq_sum_rankOne
    (L : Matrix I A ℝ) (S : Matrix A B ℝ) (R : Matrix J B ℝ)
    (i : I) (j : J) :
    latentCoincidence L S R i j =
      ∑ a : A, ∑ b : B, S a b * (L i a * R j b) := by
  unfold latentCoincidence
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end InfoGeometry.Inference.LatentCoincidenceTriFactor
