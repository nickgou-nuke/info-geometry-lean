import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite projective ratios for unnormalized systems

This file states the finite algebra directly with mathlib's canonical notation:
finite sums `∑`, real division `/`, and explicit stage maps.  It does not define
a proof-carrying system structure or local wrappers for ratios, totals, or
normalization.

The results are finite statements only: no Radon--Nikodym theorem, projective
limit measure, Cantor-boundary measure, or analytic normalization theorem is
asserted.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GromovSystem

variable {X : ℕ → Type*}

/--
If unnormalized weights are compatible with a stage map, then the ratio of two
transported weights is unchanged.
-/
theorem projective_ratio_invariant
    (measure : ∀ n, X n → ℝ) (bond : ∀ n, X n → X (n + 1))
    (compatibility : ∀ n (x : X n), measure (n + 1) (bond n x) = measure n x)
    (n : ℕ) (x y : X n) :
    measure (n + 1) (bond n x) / measure (n + 1) (bond n y) =
      measure n x / measure n y := by
  rw [compatibility n x, compatibility n y]

/--
If a transported nonzero weight is compatible but total mass changes between
finite stages, then secondary normalized ratios cannot commute with the stage
map for that state.
-/
theorem normalization_incompatibility [∀ n, Fintype (X n)]
    (measure : ∀ n, X n → ℝ) (bond : ∀ n, X n → X (n + 1))
    (compatibility : ∀ n (x : X n), measure (n + 1) (bond n x) = measure n x)
    (n : ℕ) (x : X n)
    (h_meas_nz : measure n x ≠ 0)
    (h_sum_n_nz : (∑ y : X n, measure n y) ≠ 0)
    (h_sum_n1_nz : (∑ y : X (n + 1), measure (n + 1) y) ≠ 0)
    (h_sum_change : (∑ y : X (n + 1), measure (n + 1) y) ≠
      (∑ y : X n, measure n y)) :
    measure (n + 1) (bond n x) / (∑ y : X (n + 1), measure (n + 1) y) =
        measure n x / (∑ y : X n, measure n y) → False := by
  intro h_eq
  rw [compatibility n x] at h_eq
  have h_mul :
      (measure n x / (∑ y : X (n + 1), measure (n + 1) y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) =
        (measure n x / (∑ y : X n, measure n y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) := by
    rw [h_eq]
  have h_lhs :
      (measure n x / (∑ y : X (n + 1), measure (n + 1) y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) =
        measure n x * (∑ y : X n, measure n y) := by
    field_simp [h_sum_n1_nz]
  have h_rhs :
      (measure n x / (∑ y : X n, measure n y)) *
          ((∑ y : X (n + 1), measure (n + 1) y) * (∑ y : X n, measure n y)) =
        measure n x * (∑ y : X (n + 1), measure (n + 1) y) := by
    field_simp [h_sum_n_nz]
  rw [h_lhs, h_rhs] at h_mul
  have h_sum_eq :
      (∑ y : X n, measure n y) = (∑ y : X (n + 1), measure (n + 1) y) := by
    exact mul_left_cancel₀ h_meas_nz h_mul
  exact h_sum_change h_sum_eq.symm

end GromovSystem
