import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace InfoGeometry.Canonical.CantorCuntzPotential

-- A supplied real scaling parameter for the quadratic potential.
variable (a : ℝ)

/-- A quadratic background potential. -/
def background_potential (lam : ℝ) : ℝ :=
  a * lam ^ 2

/-- The formal algebraic derivative of the background potential with respect to lam. -/
def formal_deriv_potential (lam : ℝ) : ℝ :=
  2 * a * lam

theorem hasDerivAt_background_potential (lam : ℝ) :
    HasDerivAt (background_potential a)
      (formal_deriv_potential a lam) lam := by
  have h := HasDerivAt.const_mul a ((hasDerivAt_id lam).pow 2)
  convert h using 1 <;>
    simp [background_potential, formal_deriv_potential, Function.id_def] <;>
    ring

/-- The negative formal derivative of the quadratic potential. -/
def confining_force (lam : ℝ) : ℝ :=
  - formal_deriv_potential a lam

theorem confining_force_eq_neg_two_mul (lam : ℝ) :
    confining_force a lam = -(2 * a * lam) := by
  unfold confining_force formal_deriv_potential
  rfl

theorem background_potential_nonneg
    (h_a_nonneg : 0 ≤ a) (lam : ℝ) :
    0 ≤ background_potential a lam := by
  unfold background_potential
  exact mul_nonneg h_a_nonneg (sq_nonneg lam)

theorem background_potential_pos_of_pos
    (h_a_pos : 0 < a) {lam : ℝ} (h_lam : lam ≠ 0) :
    0 < background_potential a lam := by
  unfold background_potential
  exact mul_pos h_a_pos (sq_pos_of_ne_zero h_lam)

/-- If `a ≠ 0`, the negative formal derivative vanishes only at `lam = 0`. -/
theorem trap_equilibrium (h_a_pos : a ≠ 0) (lam : ℝ) (h_eq : confining_force a lam = 0) :
    lam = 0 := by
  rw [confining_force_eq_neg_two_mul] at h_eq
  have h1 : - (2 * a * lam) = 0 := h_eq
  have h2 : 2 * a * lam = 0 := neg_eq_zero.mp h1
  cases mul_eq_zero.mp h2 with
  | inl h3 => 
    cases mul_eq_zero.mp h3 with
    | inl h4 => norm_num at h4
    | inr h5 => exact False.elim (h_a_pos h5)
  | inr h6 => exact h6

theorem confining_force_eq_zero_iff (h_a_ne_zero : a ≠ 0) (lam : ℝ) :
    confining_force a lam = 0 ↔ lam = 0 := by
  constructor
  · exact trap_equilibrium a h_a_ne_zero lam
  · intro h
    rw [h]
    simp [confining_force, formal_deriv_potential]

end InfoGeometry.Canonical.CantorCuntzPotential
