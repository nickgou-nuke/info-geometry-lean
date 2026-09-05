import InfoGeometry.Routing.FiniteSoftmax
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Positive two-boundary conditioning of a finite causal transition

A forward distribution and a backward likelihood are not two quantum states.
The backward likelihood is evaluated from an explicitly supplied boundary.
This file constructs the conditioned transition and derives normalization and
forward/backward consistency. Zero-overlap inputs are never interpreted as
conditional probabilities.
-/

noncomputable section
namespace InfoGeometry.Streaming.PositiveBoundaryConditioning

open scoped BigOperators
open InfoGeometry.Routing.FiniteSoftmax

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Native finite attention transition, using the existing softmax owner. -/
def attentionKernel (score : ι → ι → ℝ) (τ : ℝ) : Matrix ι ι ℝ :=
  fun i j => weight (score i) τ j

/-- Forward propagation of a row distribution. -/
def forward (K : Matrix ι ι ℝ) (a : ι → ℝ) : ι → ℝ :=
  fun j => ∑ i, a i * K i j

/-- Pullback of a future likelihood through one causal step. -/
def backward (K : Matrix ι ι ℝ) (b : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, K i j * b j

/-- Finite pairing of the two boundary messages. -/
def overlap (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

/-- Algebraic normalized product; probability claims require positive overlap. -/
def conditioned (a b : ι → ℝ) : ι → ℝ :=
  fun i => a i * b i / overlap a b

/-- Doob-type one-step conditioning; regularity is proved separately. -/
def tiltedKernel (K : Matrix ι ι ℝ) (b : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => K i j * b j / backward K b i

theorem attentionKernel_stochastic [Nonempty ι] (score : ι → ι → ℝ) (τ : ℝ) :
    attentionKernel score τ ∈ Matrix.rowStochastic ℝ ι := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  exact ⟨fun i j => (weight_pos (score i) τ j).le,
    fun i => weight_sum_one (score i) τ⟩

/-- The same scalar normalization is obtained before or after the causal step. -/
theorem boundary_pairing_conserved (K : Matrix ι ι ℝ) (a b : ι → ℝ) :
    overlap (forward K a) b = overlap a (backward K b) := by
  simp only [overlap, forward, backward, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem conditioned_sum (a b : ι → ℝ) (h : overlap a b ≠ 0) :
    ∑ i, conditioned a b i = 1 := by
  simp only [conditioned, ← Finset.sum_div]
  exact div_self h

theorem conditioned_nonneg (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (h : 0 < overlap a b) (i : ι) :
    0 ≤ conditioned a b i :=
  div_nonneg (mul_nonneg (ha i) (hb i)) h.le

/-- A nonzero nonnegative forward mass paired with a positive likelihood has positive overlap. -/
theorem overlap_pos (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 < b i) (i₀ : ι) (hi : 0 < a i₀) : 0 < overlap a b := by
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (ha i) (hb i).le
  · exact ⟨i₀, Finset.mem_univ _, mul_pos hi (hb i₀)⟩

/-- A hard terminal condition is allowed: only one positive component is needed. -/
theorem backward_attention_pos [Nonempty ι] (score : ι → ι → ℝ) (τ : ℝ)
    (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (j₀ : ι) (hj : 0 < b j₀) (i : ι) :
    0 < backward (attentionKernel score τ) b i := by
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (weight_pos (score i) τ j).le (hb j)
  · exact ⟨j₀, Finset.mem_univ _, mul_pos (weight_pos (score i) τ j₀) hj⟩

theorem tiltedKernel_row_sum (K : Matrix ι ι ℝ) (b : ι → ℝ) (i : ι)
    (h : backward K b i ≠ 0) : ∑ j, tiltedKernel K b i j = 1 := by
  simp only [tiltedKernel, ← Finset.sum_div]
  exact div_self h

theorem tiltedKernel_stochastic (K : Matrix ι ι ℝ) (b : ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ i, 0 < backward K b i) :
    tiltedKernel K b ∈ Matrix.rowStochastic ℝ ι := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  exact ⟨fun i j => div_nonneg (mul_nonneg (hK i j) (hb j)) (h i).le,
    fun i => tiltedKernel_row_sum K b i (ne_of_gt (h i))⟩

/-- Conditioning commutes with the one-step forward update after the kernel is tilted. -/
theorem conditioned_forward (K : Matrix ι ι ℝ) (a b : ι → ℝ)
    (h : ∀ i, backward K b i ≠ 0) :
    forward (tiltedKernel K b) (conditioned a (backward K b)) =
      conditioned (forward K a) b := by
  funext j
  change (∑ i, (a i * backward K b i / overlap a (backward K b)) *
      (K i j * b j / backward K b i)) =
    (∑ i, a i * K i j) * b j / overlap (forward K a) b
  rw [boundary_pairing_conserved]
  calc
    _ = ∑ i, (a i * K i j) * b j / overlap a (backward K b) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [div_eq_mul_inv]
      have hi := inv_mul_cancel₀ (h i)
      calc
        _ = (a i * K i j * b j * (overlap a (backward K b))⁻¹) *
            ((backward K b i)⁻¹ * backward K b i) := by ring
        _ = _ := by rw [hi, mul_one]
    _ = _ := by rw [← Finset.sum_div, ← Finset.sum_mul]

/-- Positive conditioning cannot produce anomalous values outside the observable range. -/
theorem conditioned_expectation_bounds (a b f : ι → ℝ) (l u : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hz : 0 < overlap a b)
    (hf : ∀ i, l ≤ f i ∧ f i ≤ u) :
    l ≤ ∑ i, conditioned a b i * f i ∧
      (∑ i, conditioned a b i * f i) ≤ u := by
  have hp := conditioned_nonneg a b ha hb hz
  have hs := conditioned_sum a b (ne_of_gt hz)
  constructor
  · calc
      l = (∑ i, conditioned a b i) * l := by rw [hs, one_mul]
      _ = ∑ i, conditioned a b i * l := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i).1 (hp i))
  · calc
      _ ≤ ∑ i, conditioned a b i * u :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i).2 (hp i))
      _ = (∑ i, conditioned a b i) * u := (Finset.sum_mul _ _ _).symm
      _ = u := by rw [hs, one_mul]

/-- One missing support overlap prevents probability normalization. -/
theorem conditioned_zero_overlap (a b : ι → ℝ) (h : overlap a b = 0) :
    conditioned a b = 0 := by
  funext i
  simp [conditioned, h]

end InfoGeometry.Streaming.PositiveBoundaryConditioning
