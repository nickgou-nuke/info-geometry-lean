import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.MadelungFisherRaoSynthesisBridge

/-- **Theorem 1: Madelung Amplitude-to-Density Line Element Equivalence**.
    For Madelung fluid density ρ = u^2 with amplitude u > 0 and differential dρ = 2 u du,
    the Fisher-Rao line element (dρ)^2 / ρ equals flat amplitude distance 4 (du)^2. -/
theorem madelung_fisher_rao_line_element (u du dρ : ℝ) (hu : 0 < u) (hdρ : dρ = 2 * u * du) :
    dρ * dρ / (u * u) = 4 * (du * du) := by
  have hu_ne : u * u ≠ 0 := mul_ne_zero (ne_of_gt hu) (ne_of_gt hu)
  rw [hdρ]
  have h_assoc : (2 * u * du) * (2 * u * du) / (u * u) = (4 * (du * du)) * (u * u) / (u * u) := by ring
  rw [h_assoc, mul_div_cancel_right₀ _ hu_ne]

/-- **Theorem 2: Madelung Quantum Potential Linearization Identity**.
    The Bohm-Madelung quantum potential Q = - (1/2) * (laplacian_u / u)
    satisfies the linear operator equation: 2 * u * Q + laplacian_u = 0. -/
theorem madelung_quantum_potential_linearization (u laplacian_u Q : ℝ)
    (hQ : Q = - (1 / 2) * (laplacian_u / u)) (hu : 0 < u) :
    2 * u * Q + laplacian_u = 0 := by
  have hu_ne : u ≠ 0 := ne_of_gt hu
  rw [hQ]
  calc 2 * u * (- (1 / 2) * (laplacian_u / u)) + laplacian_u
    _ = - (2 * (1 / 2)) * (u * (laplacian_u / u)) + laplacian_u := by ring
    _ = - 1 * laplacian_u + laplacian_u := by
      have h1 : 2 * (1 / 2 : ℝ) = 1 := by norm_num
      have h2 : u * (laplacian_u / u) = laplacian_u := mul_div_cancel₀ laplacian_u hu_ne
      rw [h1, h2]
    _ = 0 := by ring

end InfoGeometry.Canonical.MadelungFisherRaoSynthesisBridge
