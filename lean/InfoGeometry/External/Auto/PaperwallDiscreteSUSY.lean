import Mathlib.Tactic

/-!
# Discrete glide SUSY algebra

An abstract ring with a grading `Γ` and odd glide `G`.  Theorems prove parity
of `G²`, oddness of `Q=G`, superalgebra closure, and commutation of `Q` with
`H=G²`.
-/

noncomputable section

namespace PaperwallDiscreteSUSY

/-- Algebraic data for a glide supercharge in a ring. -/
structure GlideSUSY (R : Type*) [Ring R] where
  Γ : R
  G : R
  grading_sq : Γ * Γ = 1
  glide_odd : Γ * G + G * Γ = 0

variable {R : Type*} [Ring R]

/-- Supercharge is the odd glide. -/
def Q (S : GlideSUSY R) : R := S.G

/-- Hamiltonian/translation is the square of the glide. -/
def H (S : GlideSUSY R) : R := S.G * S.G

lemma gamma_g_eq_neg_g_gamma (S : GlideSUSY R) : S.Γ * S.G = -(S.G * S.Γ) := by
  exact eq_neg_of_add_eq_zero_left S.glide_odd

/-- `G²` is even: it commutes with the grading. -/
theorem H_is_even (S : GlideSUSY R) : S.Γ * H S - H S * S.Γ = 0 := by
  have hcomm : S.Γ * (S.G * S.G) = (S.G * S.G) * S.Γ := by
    calc
      S.Γ * (S.G * S.G) = (S.Γ * S.G) * S.G := by rw [mul_assoc]
      _ = (-(S.G * S.Γ)) * S.G := by rw [gamma_g_eq_neg_g_gamma S]
      _ = -(S.G * (S.Γ * S.G)) := by simp [mul_assoc]
      _ = -(S.G * (-(S.G * S.Γ))) := by rw [gamma_g_eq_neg_g_gamma S]
      _ = S.G * (S.G * S.Γ) := by simp
      _ = (S.G * S.G) * S.Γ := by rw [mul_assoc]
  unfold H
  exact sub_eq_zero.mpr hcomm

/-- The glide supercharge is odd. -/
theorem Q_is_odd (S : GlideSUSY R) : S.Γ * Q S + Q S * S.Γ = 0 := by
  exact S.glide_odd

/-- `N=1` closure: `{Q,Q}=2H`. -/
theorem susy_closure (S : GlideSUSY R) : Q S * Q S + Q S * Q S = (2 : ℤ) • H S := by
  unfold Q H
  abel

/-- The supercharge commutes with its square. -/
theorem Q_H_comm (S : GlideSUSY R) : Q S * H S - H S * Q S = 0 := by
  unfold Q H
  rw [mul_assoc]
  exact sub_self _

#check H_is_even
#check Q_is_odd
#check susy_closure
#check Q_H_comm

end PaperwallDiscreteSUSY
