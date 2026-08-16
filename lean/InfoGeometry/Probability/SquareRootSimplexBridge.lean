import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Probability.HomologicalProbability

/-!
# Square-root coordinates for finite probabilities

This file reuses `squareRootEmbedding` from
`InfoGeometry.Probability.Homological`.  Its normalization is
`xi i = 2 * sqrt (p i)`, so a normalized nonnegative probability vector is
sent to the sphere of squared radius `4`.

Only the finite coordinate identities are recorded here.  No claim is made
that the square-root map linearizes arbitrary Markov dynamics or produces a
global amplitude-phase product.
-/

open scoped BigOperators

namespace InfoGeometry.Probability.SquareRootSimplexBridge

open InfoGeometry.Probability.Homological

/-! ## Fisher coordinates -/

noncomputable def squareRootTangent {n : ℕ} (p v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => v i / Real.sqrt (p i)

theorem fisherMetricDiagonal_mul_sq_eq_squareRootTangent_sq
    {n : ℕ} (p v : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (i : Fin n) :
    fisherMetricDiagonal n p i * (v i) ^ 2 =
      (squareRootTangent p v i) ^ 2 := by
  simp only [fisherMetricDiagonal, if_pos (hp i)]
  unfold squareRootTangent
  rw [div_pow, Real.sq_sqrt (le_of_lt (hp i))]
  field_simp [ne_of_gt (hp i)]

theorem fisherMetricDiagonal_sum_eq_squareRootTangent_sum
    {n : ℕ} (p v : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) :
    ∑ i, fisherMetricDiagonal n p i * (v i) ^ 2 =
      ∑ i, (squareRootTangent p v i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact fisherMetricDiagonal_mul_sq_eq_squareRootTangent_sq p v hp i

theorem fisherMetricDiagonal_pos_of_pos
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (i : Fin n) :
    0 < fisherMetricDiagonal n p i := by
  simp [fisherMetricDiagonal, hp i]

theorem fisherMetricDiagonal_mul_sq_nonneg
    {n : ℕ} (p v : Fin n → ℝ) (i : Fin n) :
    0 ≤ fisherMetricDiagonal n p i * (v i) ^ 2 := by
  unfold fisherMetricDiagonal
  split_ifs with h
  · positivity
  · simp

theorem fisherMetricDiagonal_sum_sq_nonneg
    {n : ℕ} (p v : Fin n → ℝ) :
    0 ≤ ∑ i, fisherMetricDiagonal n p i * (v i) ^ 2 := by
  exact Finset.sum_nonneg (fun i _ => fisherMetricDiagonal_mul_sq_nonneg p v i)

theorem squareRootEmbedding_nonneg
    {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    0 ≤ squareRootEmbedding n p i := by
  simp [squareRootEmbedding]

theorem squareRootEmbedding_sq
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (i : Fin n) :
    (squareRootEmbedding n p i) ^ 2 = 4 * p i := by
  unfold squareRootEmbedding
  rw [mul_pow, Real.sq_sqrt (hp i)]
  norm_num

theorem squareRootEmbedding_sum_sq
    {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, (squareRootEmbedding n p i) ^ 2 = 4 := by
  calc
    ∑ i, (squareRootEmbedding n p i) ^ 2 = ∑ i, 4 * p i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact squareRootEmbedding_sq p hp i
    _ = 4 * ∑ i, p i := by
      rw [Finset.mul_sum]
    _ = 4 := by
      rw [hsum]
      norm_num

theorem squareRootEmbedding_injective_on_nonnegative
    {n : ℕ} {p q : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (h : squareRootEmbedding n p = squareRootEmbedding n q) :
    p = q := by
  funext i
  have hi := congr_fun h i
  have hsqrt : Real.sqrt (p i) = Real.sqrt (q i) := by
    dsimp [squareRootEmbedding] at hi
    linarith
  have hsquares := congrArg (fun x : ℝ => x ^ 2) hsqrt
  simpa [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)] using hsquares

/-- The inverse probability coordinate on the radius-two sphere. -/
noncomputable def amplitudeToProbability {n : ℕ} (xi : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (xi i / 2) ^ 2

theorem amplitudeToProbability_nonneg
    {n : ℕ} (xi : Fin n → ℝ) (i : Fin n) :
    0 ≤ amplitudeToProbability xi i := by
  exact sq_nonneg _

theorem amplitudeToProbability_sum_eq_one
    {n : ℕ} (xi : Fin n → ℝ)
    (hxi : ∑ i, xi i ^ 2 = 4) :
    ∑ i, amplitudeToProbability xi i = 1 := by
  calc
    ∑ i, amplitudeToProbability xi i = ∑ i, (1 / 4 : ℝ) * xi i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold amplitudeToProbability
      ring
    _ = (1 / 4 : ℝ) * ∑ i, xi i ^ 2 := by
      rw [Finset.mul_sum]
    _ = 1 := by
      rw [hxi]
      norm_num

theorem squareRootEmbedding_amplitudeToProbability
    {n : ℕ} (xi : Fin n → ℝ)
    (hxi : ∀ i, 0 ≤ xi i) :
    squareRootEmbedding n (amplitudeToProbability xi) = xi := by
  funext i
  unfold squareRootEmbedding amplitudeToProbability
  have hi : 0 ≤ xi i / 2 := by positivity
  rw [pow_two, Real.sqrt_sq hi]
  ring

theorem squareRootEmbedding_image_iff
    {n : ℕ} (xi : Fin n → ℝ) :
    (∃ p : Fin n → ℝ,
      (∀ i, 0 ≤ p i) ∧
      (∑ i, p i = 1) ∧
      squareRootEmbedding n p = xi) ↔
      ((∀ i, 0 ≤ xi i) ∧ ∑ i, xi i ^ 2 = 4) := by
  constructor
  · rintro ⟨p, hp, hsum, hmap⟩
    constructor
    · intro i
      rw [← congr_fun hmap i]
      exact squareRootEmbedding_nonneg p i
    · rw [← hmap]
      exact squareRootEmbedding_sum_sq p hp hsum
  · intro hxi
    refine ⟨amplitudeToProbability xi, ?_,
      amplitudeToProbability_sum_eq_one xi hxi.2, ?_⟩
    · exact fun i => amplitudeToProbability_nonneg xi i
    · exact squareRootEmbedding_amplitudeToProbability xi hxi.1

end InfoGeometry.Probability.SquareRootSimplexBridge
