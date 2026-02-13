import Mathlib

section LargeDeviations

/-- Finite-parameter Cramér transform (Legendre-Fenchel on a finite grid `Θ`). -/
noncomputable def cramerRateOn
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η : ℝ) : ℝ :=
  Θ.sup' hΘ (fun θ => η * θ - ψ θ)

lemma le_cramerRateOn
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η θ : ℝ)
    (hθ : θ ∈ Θ) :
    η * θ - ψ θ ≤ cramerRateOn Θ hΘ ψ η := by
  unfold cramerRateOn
  exact Finset.le_sup' (f := fun t => η * t - ψ t) hθ

lemma fenchelYoung_on_cramerRateOn
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η θ : ℝ)
    (hθ : θ ∈ Θ) :
    η * θ ≤ ψ θ + cramerRateOn Θ hΘ ψ η := by
  have h := le_cramerRateOn Θ hΘ ψ η θ hθ
  linarith

lemma cramerRateOn_eq_of_mem_and_max
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η θ0 : ℝ)
    (hθ0 : θ0 ∈ Θ)
    (hmax : ∀ θ, θ ∈ Θ → η * θ - ψ θ ≤ η * θ0 - ψ θ0) :
    cramerRateOn Θ hΘ ψ η = η * θ0 - ψ θ0 := by
  apply le_antisymm
  · unfold cramerRateOn
    exact Finset.sup'_le (s := Θ) (f := fun θ => η * θ - ψ θ) hΘ (by
      intro θ hθ
      exact hmax θ hθ)
  · exact le_cramerRateOn Θ hΘ ψ η θ0 hθ0

end LargeDeviations
