import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Algebra.BostConnesGalois

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def cyclotomicPhase (r : ℚ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) : ℂ))

def galoisAction (g : ℤ) (r : ℚ) : ℚ :=
  (g : ℚ) * r

def semigroupEndo (n : ℕ) (r : ℚ) : ℚ :=
  r / (n : ℚ)

theorem galois_semigroup_equivariance (g : ℤ) (n : ℕ) (r : ℚ) :
    galoisAction g (semigroupEndo n r) = semigroupEndo n (galoisAction g r) := by
  unfold galoisAction semigroupEndo
  ring

theorem cyclotomic_phase_unitary (r : ℚ) :
    ‖cyclotomicPhase r‖ = 1 := by
  unfold cyclotomicPhase
  have h_re : (2 * Real.pi * Complex.I * ((r : ℝ) : ℂ)).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_norm := Complex.norm_exp (2 * Real.pi * Complex.I * ((r : ℝ) : ℂ))
  rw [h_re, Real.exp_zero] at h_norm
  exact h_norm
