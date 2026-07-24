import Mathlib
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture

noncomputable section
namespace InfoGeometry.Thermo.ModularFirstLaw

def entropy (expectK : ℝ) : ℝ := expectK

lemma deriv_eq_of_fun_eq {f g : ℝ → ℝ} (hfg : ∀ x, f x = g x) (x : ℝ) :
    deriv f x = deriv g x := by
  have h₁ : f = g := funext hfg
  have h₂ : deriv f x = deriv g x := by
    apply congr_arg (fun h => deriv h x)
    exact h₁
  exact h₂

theorem first_law_normalized_States {S K : ℝ → ℝ} 
    (hSK : ∀ t, S t = K t)  -- S(t) = K(t) for normalized states
    (hS : Differentiable ℝ S) 
    (hK : Differentiable ℝ K) :
    ∀ x : ℝ, deriv S x = deriv K x := by
  intro x
  have h₁ : S = K := by
    funext t
    apply hSK
  have h₂ : DifferentiableAt ℝ S x := hS x
  have h₃ : DifferentiableAt ℝ K x := hK x
  have h₄ : deriv S x = deriv K x := by
    have h₅ : S = K := h₁
    have h₆ : ∀ x, S x = K x := by
      intro x
      rw [h₅]
    exact deriv_eq_of_fun_eq h₆ x
  exact h₄

end InfoGeometry.Thermo.ModularFirstLaw
