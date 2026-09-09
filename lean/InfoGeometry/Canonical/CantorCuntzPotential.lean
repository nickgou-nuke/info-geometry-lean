import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.CantorCuntzPotential

-- A supplied real scaling parameter for the quadratic potential.
variable (a : ℝ)

/-- A quadratic background potential. -/
def background_potential (lam : ℝ) : ℝ :=
  a * lam ^ 2

/-- The formal algebraic derivative of the background potential with respect to lam. -/
def formal_deriv_potential (lam : ℝ) : ℝ :=
  2 * a * lam

/-- The negative formal derivative of the quadratic potential. -/
def confining_force (lam : ℝ) : ℝ :=
  - formal_deriv_potential a lam

/-- If `a ≠ 0`, the negative formal derivative vanishes only at `lam = 0`. -/
theorem trap_equilibrium (h_a_pos : a ≠ 0) (lam : ℝ) (h_eq : confining_force a lam = 0) :
    lam = 0 := by
  unfold confining_force formal_deriv_potential at h_eq
  have h1 : - (2 * a * lam) = 0 := h_eq
  have h2 : 2 * a * lam = 0 := neg_eq_zero.mp h1
  cases mul_eq_zero.mp h2 with
  | inl h3 => 
    cases mul_eq_zero.mp h3 with
    | inl h4 => norm_num at h4
    | inr h5 => exact False.elim (h_a_pos h5)
  | inr h6 => exact h6

end InfoGeometry.Canonical.CantorCuntzPotential
