import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Contact-anchored rank-one scale and zero-intercept response

This file formalizes the algebraic core of the Eu-152 scale audit.  It does
not promote numerical SVD output to a theorem: the kernel-checked statements
are the exact separability, quadratic restoration, and origin-slope identities
that the numerical fit tests.
-/
namespace InfoGeometry.Probability.DetectorRankOneScale

noncomputable section

open scoped BigOperators

/-- A separable energy-by-acquisition response matrix. -/
def separableMatrix {m n : ℕ} (a : Fin m → ℝ) (s : Fin n → ℝ) :
    Fin m → Fin n → ℝ := fun i j => a i * s j

/-- Exact rank-one cross-product identity for every 2-by-2 minor. -/
theorem separable_cross_product {m n : ℕ} (a : Fin m → ℝ) (s : Fin n → ℝ)
    (i k : Fin m) (j l : Fin n) :
    separableMatrix a s i j * separableMatrix a s k l =
      separableMatrix a s i l * separableMatrix a s k j := by
  simp [separableMatrix]
  ring

/-- The observed quadratic response and its restored first-order response. -/
def quadraticResponse (C K X : ℝ) : ℝ := C * X - K * X ^ 2

def restoredResponse (R K X : ℝ) : ℝ := R + K * X ^ 2

/-- Adding the fitted quadratic loss returns the first-order ray exactly. -/
theorem restored_quadraticResponse (C K X : ℝ) :
    restoredResponse (quadraticResponse C K X) K X = C * X := by
  simp [restoredResponse, quadraticResponse]


/-- The origin-constrained least-squares slope. -/
def originSlope {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i, x i * y i) / (∑ i, x i * x i)

/-- If all observations lie on the ray `y = γ x`, the origin slope is γ. -/
theorem originSlope_exact {n : ℕ} (x y : Fin n → ℝ) (γ : ℝ)
    (hline : ∀ i, y i = γ * x i)
    (hden : (∑ i, x i * x i) ≠ 0) :
    originSlope x y = γ := by
  unfold originSlope
  have hnum : (∑ i, x i * y i) = γ * (∑ i, x i * x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hline i]
    ring
  rw [hnum]
  have hden' : (∑ i, x i ^ 2) ≠ 0 := by simpa [pow_two] using hden
  field_simp [hden']

/-- Contact anchoring fixes the scale of a positive rank-one factorization. -/
theorem contact_anchor_unique {n : ℕ} (s t : Fin n → ℝ) (j₀ : Fin n)
    (hs : 0 < s j₀) (ht : 0 < t j₀)
    (hscale : ∀ j, s j / s j₀ = t j / t j₀) :
    ∀ j, s j = (s j₀ / t j₀) * t j := by
  intro j
  have h := hscale j
  field_simp [ne_of_gt hs, ne_of_gt ht] at h
  field_simp [ne_of_gt hs, ne_of_gt ht]
  exact h

end

end InfoGeometry.Probability.DetectorRankOneScale
