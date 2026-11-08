import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.FourierTripartiteSlicing

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def half : R := algebraMap ℂ R (1 / 2)

def P_vac (X : R) : R := 1 - X^4

def P_sym (X : R) : R := half * (X^4 + X^2)

def P_anti (X : R) : R := half * (X^4 - X^2)

theorem half_add_half : half + half = (1 : R) := by
  unfold half
  rw [← map_add]
  have : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by ring
  rw [this, map_one]

theorem completeness (X : R) : P_vac X + P_sym X + P_anti X = 1 := by
  unfold P_vac P_sym P_anti
  calc 1 - X^4 + half * (X^4 + X^2) + half * (X^4 - X^2)
    _ = 1 - X^4 + (half * X^4 + half * X^2) + (half * X^4 - half * X^2) := by ring
    _ = 1 - X^4 + (half + half) * X^4 := by ring
    _ = 1 - X^4 + 1 * X^4 := by rw [half_add_half]
    _ = 1 := by ring

theorem orthogonal_sym_anti (X : R) : 
    P_sym X * P_anti X = half * half * (X^8 - X^4) := by
  unfold P_sym P_anti
  ring

theorem orthogonal_sym_anti_of_X5_eq_X (X : R) (h : X^5 = X) : 
    P_sym X * P_anti X = 0 := by
  have h8 : X^8 = X^4 := by
    calc X^8 = X^5 * X^3 := by ring
      _ = X * X^3 := by rw [h]
      _ = X^4 := by ring
  rw [orthogonal_sym_anti, h8, sub_self, mul_zero]
