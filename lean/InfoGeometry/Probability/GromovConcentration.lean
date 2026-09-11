import Mathlib.Data.Fintype.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Finite weighted concentration bound on a discrete space

This module states the weighted finite Chebyshev-style inequality directly with
mathlib's canonical finite sums, filters, real absolute value, and powers.  It
introduces no local second-moment or outlier-weight wrapper definitions.

This is a finite algebraic inequality only, not a full asymptotic Lévy-family or
metric-measure concentration theorem.
-/

set_option autoImplicit false

namespace Gromov.Concentration

open Finset
open scoped BigOperators

variable {M : Type*} [Fintype M] [DecidableEq M]

omit [DecidableEq M] in
/-- Discrete weighted concentration: outliers are controlled by the second moment. -/
theorem unnormalized_concentration_inequality
    (w : M → ℝ) (f : M → ℝ) (μ : ℝ) (ε : ℝ)
    (h_nonneg : ∀ x, 0 ≤ w x) (h_eps : 0 < ε) :
    (∑ x ∈ Finset.univ.filter (fun x => ε ≤ |f x - μ|), w x) * ε^2 ≤
      ∑ x : M, w x * (f x - μ)^2 := by
  classical
  let S : Finset M := Finset.univ.filter (fun x => ε ≤ |f x - μ|)
  have hS : Finset.sum S (fun x => w x * ε^2) ≤
      Finset.sum S (fun x => w x * (f x - μ)^2) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    have hx' : ε ≤ |f x - μ| := by
      simpa [S] using (Finset.mem_filter.mp hx).2
    have hsq : ε^2 ≤ (f x - μ)^2 := by
      have hsqabs : ε^2 ≤ |f x - μ|^2 := by
        exact (sq_le_sq₀ (le_of_lt h_eps) (abs_nonneg _)).2 hx'
      simpa [sq_abs] using hsqabs
    exact mul_le_mul_of_nonneg_left hsq (h_nonneg x)
  have hS' : Finset.sum S (fun x => w x * (f x - μ)^2) ≤
      Finset.sum Finset.univ (fun x => w x * (f x - μ)^2) := by
    exact Finset.sum_le_univ_sum_of_nonneg
      (s := S) (f := fun x => w x * (f x - μ)^2)
      (by intro x; exact mul_nonneg (h_nonneg x) (sq_nonneg _))
  calc
    (∑ x ∈ Finset.univ.filter (fun x => ε ≤ |f x - μ|), w x) * ε^2
        = Finset.sum S (fun x => w x) * ε^2 := by
            simp [S]
    _ = Finset.sum S (fun x => w x * ε^2) := by
            simpa using (Finset.sum_mul S (fun x => w x) (ε^2))
    _ ≤ Finset.sum S (fun x => w x * (f x - μ)^2) := hS
    _ ≤ Finset.sum Finset.univ (fun x => w x * (f x - μ)^2) := hS'
    _ = ∑ x : M, w x * (f x - μ)^2 := by
            rfl

end Gromov.Concentration
