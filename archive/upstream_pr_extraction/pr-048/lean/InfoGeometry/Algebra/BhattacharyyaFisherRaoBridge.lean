import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.BhattacharyyaFisherRaoBridge

/-- **Definition**: Discrete Bhattacharyya Coefficient between Probability Vectors p and q.
    BC(p, q) = ∑_{i} √(p_i * q_i). -/
def bhattacharyyaCoeff {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => Real.sqrt (p i * q i))

/-- **Definition**: Square-Root Probability Amplitude Vector ψ_i = √(p_i). -/
def amplitude {n : ℕ} (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (p i)

/-- **Theorem**: Amplitude Normalization on L2 Unit Sphere.
    If ∑_{i} p_i = 1 and p_i ≥ 0, then ∑_{i} (ψ_i)^2 = 1. -/
theorem amplitude_l2_normalization {n : ℕ} (p : Fin n → ℝ) (hp_pos : ∀ i, 0 ≤ p i)
    (hp_sum : (Finset.univ : Finset (Fin n)).sum p = 1) :
    (Finset.univ : Finset (Fin n)).sum (fun i => (amplitude p i)^2) = 1 := by
  dsimp [amplitude]
  have h_sq : ∀ i, (Real.sqrt (p i))^2 = p i := fun i => Real.sq_sqrt (hp_pos i)
  calc (Finset.univ : Finset (Fin n)).sum (fun i => (Real.sqrt (p i))^2)
    _ = (Finset.univ : Finset (Fin n)).sum p := by
      congr 1
      ext i
      exact h_sq i
    _ = 1 := hp_sum

/-- **Theorem**: Bhattacharyya Coefficient is L2 Amplitude Inner Product.
    BC(p, q) = ⟨amplitude p, amplitude q⟩ = ∑_{i} √(p_i) √(q_i). -/
theorem bhattacharyya_eq_amplitude_inner_product {n : ℕ} (p q : Fin n → ℝ)
    (hp_pos : ∀ i, 0 ≤ p i) :
    bhattacharyyaCoeff p q = (Finset.univ : Finset (Fin n)).sum (fun i => amplitude p i * amplitude q i) := by
  dsimp [bhattacharyyaCoeff, amplitude]
  congr 1
  ext i
  rw [Real.sqrt_mul (hp_pos i)]

/-- **Theorem**: Infinitesimal Fisher-Rao Differential Metric Equivalence.
    For u = √p and du = d√p, 4 u^2 (du)^2 = (dp)^2,
    which yields the Fisher-Rao metric element (dp)^2 / p = 4 (d√p)^2. -/
theorem fisher_rao_infinitesimal_metric_element (u du dp : ℝ)
    (h_diff : 2 * u * du = dp) :
    4 * (u * u) * (du * du) = dp * dp := by
  calc 4 * (u * u) * (du * du)
    _ = (2 * u * du) * (2 * u * du) := by ring
    _ = dp * dp := by rw [h_diff]

end InfoGeometry.Algebra.BhattacharyyaFisherRaoBridge
