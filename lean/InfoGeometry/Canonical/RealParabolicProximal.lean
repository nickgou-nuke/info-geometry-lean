import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite real parabolic proximal transport

This is the algebraic finite shadow of the proximal/JKO shear interface.  It
contains only the exact real matrix identities.  No Wasserstein space, heat
equation, minimizer, or continuum limit is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealParabolicProximal

def step (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, η; 0, 1]

theorem step_comp (η₁ η₂ : ℝ) :
    step η₁ * step η₂ = step (η₁ + η₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [step, Matrix.mul_apply, Fin.sum_univ_two]
  · ring

theorem step_zero : step 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [step]

theorem step_neg_comp (η : ℝ) :
    step (-η) * step η = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [step_comp]
  simp [step_zero]

theorem step_comp_neg (η : ℝ) :
    step η * step (-η) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [step_comp]
  simp [step_zero]

theorem step_pow (η : ℝ) (n : ℕ) :
    step η ^ n = step ((n : ℝ) * η) := by
  induction n with
  | zero => simp [step_zero]
  | succ n ih =>
      rw [pow_succ, ih, step_comp]
      congr 1
      push_cast
      ring

theorem step_accumulated_shear (η : ℝ) (n : ℕ) :
    (step η ^ n) 0 1 = (n : ℝ) * η := by
  rw [step_pow]
  simp [step]

theorem step_inverse (η : ℝ) :
    (step η)⁻¹ = step (-η) := by
  apply Matrix.inv_eq_right_inv
  exact step_comp_neg η

end InfoGeometry.Canonical.RealParabolicProximal

end noncomputable section
