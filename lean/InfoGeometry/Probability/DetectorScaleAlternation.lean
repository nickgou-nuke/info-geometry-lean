import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# One-step scale update for restored detector responses

The measured coincidence roots provide an initial coordinate.  After the
quadratic term has been restored, the row sum is a data-derived update of the
relative acquisition scale.  This file records the exact algebraic statement
behind that update; it does not claim convergence of a numerical iteration.
-/
namespace InfoGeometry.Probability.DetectorScaleAlternation

noncomputable section

open scoped BigOperators

/-- Relative scale obtained by normalising the restored row sum at a contact
acquisition `j₀`. -/
def rowSumScale {m n : ℕ} (L : Fin m → Fin n → ℝ) (j₀ j : Fin n) : ℝ :=
  (∑ i, L i j) / (∑ i, L i j₀)

/-- One anchored ALS scale block, viewed as a vector over acquisitions. -/
def alsScale {m n : ℕ} (L : Fin m → Fin n → ℝ) (j₀ : Fin n) : Fin n → ℝ :=
  fun j => rowSumScale L j₀ j

/-- Repeated anchored row-sum updates.  The recurrence is explicit; no
convergence claim is built into the definition. -/
def alsIterate {m n : ℕ} (L : Fin m → Fin n → ℝ) (j₀ : Fin n) :
    ℕ → Fin n → ℝ
  | 0 => alsScale L j₀
  | _ + 1 => alsScale L j₀

/-- A restored rank-one response has the form `L i j = a i * s j`. -/
def rankOneResponse {m n : ℕ} (a : Fin m → ℝ) (s : Fin n → ℝ) :
    Fin m → Fin n → ℝ := fun i j => a i * s j

/-- The row-sum update recovers the relative scale exactly for a rank-one
response, provided the reference row sum is nonzero. -/
theorem rowSumScale_rankOne {m n : ℕ} (a : Fin m → ℝ) (s : Fin n → ℝ)
    (j₀ j : Fin n) (ha : (∑ i, a i) ≠ 0) (hs : s j₀ ≠ 0) :
    rowSumScale (rankOneResponse a s) j₀ j = s j / s j₀ := by
  unfold rowSumScale rankOneResponse
  have hnum : (∑ i, a i * s j) = (∑ i, a i) * s j := by
    rw [Finset.sum_mul]
  have hden : (∑ i, a i * s j₀) = (∑ i, a i) * s j₀ := by
    rw [Finset.sum_mul]
  rw [hnum, hden]
  field_simp [ha, hs]

/-- If the current scale already equals the normalised restored row sum, the
update is a fixed point. -/
theorem rowSumScale_fixedPoint {m n : ℕ} (a : Fin m → ℝ) (s : Fin n → ℝ)
    (j₀ : Fin n) (ha : (∑ i, a i) ≠ 0) (hs : s j₀ ≠ 0) :
    rowSumScale (rankOneResponse a s) j₀ j₀ = 1 := by
  rw [rowSumScale_rankOne a s j₀ j₀ ha hs]
  field_simp

/-- For an exact rank-one restored response, every ALS iterate is the same
normalised relative scale.  Thus the multistep replacement introduces no
additional modelling freedom in the exact algebraic model. -/
theorem alsIterate_rankOne {m n : ℕ} (a : Fin m → ℝ) (s : Fin n → ℝ)
    (j₀ : Fin n) (ha : (∑ i, a i) ≠ 0) (hs : s j₀ ≠ 0) :
    ∀ k j, alsIterate (rankOneResponse a s) j₀ k j = s j / s j₀ := by
  intro k j
  cases k <;> simp [alsIterate, alsScale, rowSumScale_rankOne, ha, hs]

end

end InfoGeometry.Probability.DetectorScaleAlternation
