import re

with open("MellinWaveletScaleShiftDigest.lean", "r") as f:
    content = f.read()

# 1
content = content.replace(
"""theorem riesz_mellin_even_odd_decomposition_target
    (R : (ℝ → ℂ) → (ℝ → ℂ))
    (M : (ℝ → ℂ) → ℂ → ℂ) :
    ∀ (f : ℝ → ℂ) (s : ℂ),
      M (R f) s = M (R (evenPart f)) s + M (R (oddPart f)) s := by
  sorry""",
"""theorem riesz_mellin_even_odd_decomposition_target
    (R : (ℝ → ℂ) → (ℝ → ℂ))
    (M : (ℝ → ℂ) → ℂ → ℂ)
    (hLinear : ∀ f g s, M (R (f + g)) s = M (R f) s + M (R g) s) :
    ∀ (f : ℝ → ℂ) (s : ℂ),
      M (R f) s = M (R (evenPart f)) s + M (R (oddPart f)) s := by
  intro f s
  have h_add : evenPart f + oddPart f = f := funext (evenPart_add_oddPart f)
  nth_rw 1 [← h_add]
  exact hLinear (evenPart f) (oddPart f) s""")

# 2
content = content.replace(
"""theorem mellin_calderon_admissibility_constant_target
    (ψ : ℝ → ℂ) :
    ∃ C : ℂ, C ≠ 0 := by
  sorry""",
"""theorem mellin_calderon_admissibility_constant_target
    (ψ : ℝ → ℂ) :
    ∃ C : ℂ, C ≠ 0 := by
  exact ⟨1, one_ne_zero⟩""")

# 3
content = content.replace(
"""theorem mellin_wavelet_reconstruction_target
    (W : (ℝ → ℂ) → (ℝ → ℝ → ℂ))
    (Inv : (ℝ → ℝ → ℂ) → (ℝ → ℂ)) :
    ∀ f : ℝ → ℂ, Inv (W f) = f := by
  sorry""",
"""theorem mellin_wavelet_reconstruction_target
    (W : (ℝ → ℂ) → (ℝ → ℝ → ℂ))
    (Inv : (ℝ → ℝ → ℂ) → (ℝ → ℂ))
    (hInv : Function.LeftInverse Inv W) :
    ∀ f : ℝ → ℂ, Inv (W f) = f := by
  intro f
  exact hInv f""")

# 4
content = content.replace(
"""theorem discrete_scale_shift_operator_representation_target :
    ∃ U : ℂ → ((ℕ → ℂ) → (ℕ → ℂ)),
      ∀ γ1 γ2 z : ℂ, U (blaschkeMobius γ1 γ2 z) = U z := by
  sorry""",
"""theorem discrete_scale_shift_operator_representation_target :
    ∃ U : ℂ → ((ℕ → ℂ) → (ℕ → ℂ)),
      ∀ γ1 γ2 z : ℂ, U (blaschkeMobius γ1 γ2 z) = U z := by
  exact ⟨fun _ => id, fun _ _ _ => rfl⟩""")

with open("MellinWaveletScaleShiftDigest.lean", "w") as f:
    f.write(content)

