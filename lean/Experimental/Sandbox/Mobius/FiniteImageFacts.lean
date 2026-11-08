import Experimental.Sandbox.Mobius.FiniteInjective

namespace Experimental.Sandbox.Mobius

lemma den_ne_zero_of_eval_some_eq_some
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (h : M.eval (some z) = some w) :
    M.c * z + M.d ≠ 0 := by
  have hne : M.eval (some z) ≠ none := by
    rw [h]
    simp
  exact (eval_some_ne_none_iff M z).mp hne

lemma eval_some_eq_some_iff
    (M : InfoGeometry.MobiusTransform) (z w : ℂ) :
    M.eval (some z) = some w ↔
      M.c * z + M.d ≠ 0 ∧ w = (M.a * z + M.b) / (M.c * z + M.d) := by
  constructor
  · intro h
    have hden := den_ne_zero_of_eval_some_eq_some M z w h
    have hf := eval_some_eq_fractional_of_den_ne_zero M z hden
    injection h.symm.trans hf with hw
    exact ⟨hden, hw⟩
  · intro h
    rw [h.2]
    exact eval_some_eq_fractional_of_den_ne_zero M z h.1

lemma eval_some_value_unique
    (M : InfoGeometry.MobiusTransform) (z w₁ w₂ : ℂ)
    (h₁ : M.eval (some z) = some w₁) (h₂ : M.eval (some z) = some w₂) :
    w₁ = w₂ := by
  rw [h₁] at h₂
  injection h₂

lemma finite_eval_outputs_eq_iff
    (M : InfoGeometry.MobiusTransform) (z₁ z₂ w₁ w₂ : ℂ)
    (h₁ : M.eval (some z₁) = some w₁) (h₂ : M.eval (some z₂) = some w₂) :
    w₁ = w₂ ↔ z₁ = z₂ := by
  constructor
  · intro hw
    have hz₁ := den_ne_zero_of_eval_some_eq_some M z₁ w₁ h₁
    have hz₂ := den_ne_zero_of_eval_some_eq_some M z₂ w₂ h₂
    have heval : M.eval (some z₁) = M.eval (some z₂) := by
      rw [h₁, h₂, hw]
    exact eval_some_injective_of_den_ne_zero M z₁ z₂ hz₁ hz₂ heval
  · intro hz
    subst z₂
    exact eval_some_value_unique M z₁ w₁ w₂ h₁ h₂

lemma finite_eval_outputs_ne_of_inputs_ne
    (M : InfoGeometry.MobiusTransform) (z₁ z₂ w₁ w₂ : ℂ)
    (h₁ : M.eval (some z₁) = some w₁) (h₂ : M.eval (some z₂) = some w₂)
    (hz : z₁ ≠ z₂) :
    w₁ ≠ w₂ := by
  intro hw
  exact hz ((finite_eval_outputs_eq_iff M z₁ z₂ w₁ w₂ h₁ h₂).mp hw)

end Experimental.Sandbox.Mobius
