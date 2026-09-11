import Mathlib.Data.Finset.Lattice.Fold
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace InfoGeometry

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

lemma exists_mem_eq_cramerRateOn
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η : ℝ) :
    ∃ θ0, θ0 ∈ Θ ∧ cramerRateOn Θ hΘ ψ η = η * θ0 - ψ θ0 := by
  unfold cramerRateOn
  rcases Finset.exists_mem_eq_sup' (s := Θ) (H := hΘ) (f := fun θ => η * θ - ψ θ) with
    ⟨θ0, hθ0, hθ0eq⟩
  exact ⟨θ0, hθ0, hθ0eq⟩

lemma exists_argmax_cramerRateOn
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η : ℝ) :
    ∃ θ0, θ0 ∈ Θ ∧ ∀ θ, θ ∈ Θ → η * θ - ψ θ ≤ η * θ0 - ψ θ0 := by
  rcases exists_mem_eq_cramerRateOn Θ hΘ ψ η with ⟨θ0, hθ0, hθ0eq⟩
  refine ⟨θ0, hθ0, ?_⟩
  intro θ hθ
  have hle : η * θ - ψ θ ≤ cramerRateOn Θ hΘ ψ η := le_cramerRateOn Θ hΘ ψ η θ hθ
  simpa [hθ0eq] using hle

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

lemma cramerRateOn_singleton (θ0 : ℝ) (ψ : ℝ → ℝ) (η : ℝ) :
    cramerRateOn ({θ0} : Finset ℝ) (by simp) ψ η = η * θ0 - ψ θ0 := by
  apply cramerRateOn_eq_of_mem_and_max
  · simp
  · intro θ hθ
    rcases Finset.mem_singleton.mp hθ with rfl
    exact le_rfl

end LargeDeviations

end InfoGeometry
