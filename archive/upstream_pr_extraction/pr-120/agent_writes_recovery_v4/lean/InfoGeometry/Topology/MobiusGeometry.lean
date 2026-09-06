    (H 0 0) + (H 1 1) = 2 := by
  dsimp [parabolicNormalForm]
  ring

lemma parabolic_det (β γ : ℂ) :
    let H := parabolicNormalForm β γ
    (H 0 0) * (H 1 1) - (H 0 1) * (H 1 0) = 1 := by
  dsimp [parabolicNormalForm]
  ring

-- Non-parabolic (dilation/rotation) normal form H(k; γ₁, γ₂)
def nonParabolicNormalForm (k γ₁ γ₂ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![γ₁ - k * γ₂, (k - 1) * γ₁ * γ₂],
    ![1 - k, k * γ₁ - γ₂]]

-- Eigenvalue mapping: λ_i = c γ_i + d
lemma eigenvalue_mapping (a b c d λ γ : ℂ) (h_fixed : c * γ^2 + (d - a) * γ - b = 0) (h_eigen : λ = c * γ + d) :
    λ^2 - (a + d) * λ + (a * d - b * c) = 0 := by
  calc λ^2 - (a + d) * λ + (a * d - b * c)
    _ = (c * γ + d)^2 - (a + d) * (c * γ + d) + (a * d - b * c) := by rw [h_eigen]
    _ = c * (c * γ^2 + (d - a) * γ - b) := by ring
    _ = c * 0 := by rw [h_fixed]
    _ = 0 := by ring

-- Circle-Preserving Theorem: Decomposition of Möbius transformations
def trans_f1 (c d z : ℂ) := z + d / c
def inv_f2 (z : ℂ) := z⁻¹
def dil_f3 (a b c d z : ℂ) := ((b * c - a * d) / c^2) * z
def trans_f4 (a c z : ℂ) := z + a / c

lemma mobius_decomposition (a b c d z : ℂ) (hc : c ≠ 0) (hz : c * z + d ≠ 0) :
The above content does NOT show the entire file contents. If you need to view any lines of the file which were not shown to complete your task, call this tool again to view those lines.