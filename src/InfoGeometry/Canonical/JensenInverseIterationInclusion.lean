import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Jensen inverse-iteration inclusion data

Finite formalization surface for Paul S. Jensen, "An Inclusion Theorem Related to
Inverse Iteration" (Linear Algebra Appl. 6, 209--215, 1973).

The paper proves that inverse iteration for a real symmetric generalized
eigenproblem `(A - λ M)x = 0`, with `M` positive definite, produces inclusion
intervals `[μ - b_j, μ + b_j]` and an accelerated family
`[μ - δ_j, μ + δ_j]` with `δ_j < b_j` after stage `j ≥ 3`.

This file is theorem-safe: it does not reprove the full spectral theorem,
Rayleigh quotient iteration, or numerical convergence.  It records Jensen's
polynomial and packages the analytic/spectral hypotheses as explicit fields;
the Lean kernel proves the interval readouts used downstream.
-/

namespace InfoGeometry.Canonical.JensenInverseIterationInclusion

noncomputable section

open scoped BigOperators

/-- Closed interval membership, written as a proposition to avoid interval APIs. -/
def InClosedInterval (left right x : ℝ) : Prop :=
  left ≤ x ∧ x ≤ right

/-- If `|x - μ| ≤ r`, then `x ∈ [μ-r, μ+r]`. -/
theorem mem_centered_interval_of_abs_sub_le
    {μ x r : ℝ} (h : |x - μ| ≤ r) :
    InClosedInterval (μ - r) (μ + r) x := by
  constructor
  · have hleft : -r ≤ x - μ := (abs_le.mp h).1
    linarith
  · have hpos : x - μ ≤ r := (abs_le.mp h).2
    linarith

/-- Jensen's quadratic polynomial from equation (6) of the paper. -/
def jensenPolynomial (b : ℕ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  - (b (j - 1) - b j) * z ^ 2
    + b (j - 1) * (b (j - 2) - b j) * z
    - b (j - 1) * b j * (b (j - 2) - b (j - 1))

/-- The discriminant/radicand appearing in Jensen's smaller-root formula. -/
def jensenRadicand (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  (b (j - 2) - b j) ^ 2
    - 4 * (b (j - 1) - b j) * (b (j - 2) - b (j - 1)) * (b j / b (j - 1))

/--
The explicit accelerated radius formula corresponding to Jensen's smaller root.
The formula is meaningful under the monotonicity/positivity premises supplied in
`JensenAcceleratedInclusionData`.
-/
def acceleratedRadiusFormula (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  b (j - 1) *
    ((b (j - 2) - b j) - Real.sqrt (jensenRadicand b j)) /
      (2 * (b (j - 1) - b j))

/-- Finite generalized symmetric eigenproblem carrier. -/
structure GeneralizedSymmetricEigenproblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  M : Matrix (Fin n) (Fin n) ℝ
  symm_A : A.IsSymm
  symm_M : M.IsSymm
  positive_M : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M.mulVec x)

namespace GeneralizedSymmetricEigenproblem

variable {n : ℕ} (E : GeneralizedSymmetricEigenproblem n)

/-- A scalar/vector pair solving the generalized eigenproblem. -/
def IsEigenpair (lam : ℝ) (x : Fin n → ℝ) : Prop :=
  x ≠ 0 ∧ E.A.mulVec x = lam • E.M.mulVec x

end GeneralizedSymmetricEigenproblem

/--
Jensen-style inverse-iteration data at finite dimension.  The convergence and
spectral-minimum facts are supplied by an owner proof or numerical certificate.
-/
structure JensenInverseIterationData (n : ℕ) where
  problem : GeneralizedSymmetricEigenproblem n
  shift : ℝ
  iterate : ℕ → Fin n → ℝ
  normalization : ℕ → ℝ
  radius : ℕ → ℝ
  targetEigenvalue : ℝ
  targetEigenvector : Fin n → ℝ
  target_is_eigenpair :
    GeneralizedSymmetricEigenproblem.IsEigenpair problem targetEigenvalue targetEigenvector
  radius_bounds_target : ∀ j : ℕ,
    |targetEigenvalue - shift| ≤ radius j

namespace JensenInverseIterationData

variable {n : ℕ} (D : JensenInverseIterationData n)

/-- The unaccelerated inverse-iteration radius gives Jensen's inclusion interval. -/
theorem target_mem_unaccelerated_interval (j : ℕ) :
    InClosedInterval (D.shift - D.radius j) (D.shift + D.radius j)
      D.targetEigenvalue :=
  mem_centered_interval_of_abs_sub_le (D.radius_bounds_target j)

end JensenInverseIterationData

/--
Accelerated Jensen inclusion certificate.  The field `accelerated_is_smaller_root`
connects the chosen accelerated radius with the quadratic from equation (6), and
`accelerated_bounds_target` records the spectral conclusion of Jensen's theorem.
-/
structure JensenAcceleratedInclusionData (n : ℕ)
    extends JensenInverseIterationData n where
  acceleratedRadius : ℕ → ℝ
  accelerated_eq_formula : ∀ j : ℕ, 3 ≤ j →
    acceleratedRadius j = acceleratedRadiusFormula radius j
  accelerated_is_smaller_root : ∀ j : ℕ, 3 ≤ j →
    jensenPolynomial radius j (acceleratedRadius j) = 0
  accelerated_le_unaccelerated : ∀ j : ℕ, 3 ≤ j →
    acceleratedRadius j ≤ radius j
  accelerated_nonneg : ∀ j : ℕ, 3 ≤ j → 0 ≤ acceleratedRadius j
  accelerated_bounds_target : ∀ j : ℕ, 3 ≤ j →
    |targetEigenvalue - shift| ≤ acceleratedRadius j

namespace JensenAcceleratedInclusionData

variable {n : ℕ} (D : JensenAcceleratedInclusionData n)

/-- Jensen's accelerated radius is a root of the stage quadratic. -/
theorem accelerated_radius_root (j : ℕ) (hj : 3 ≤ j) :
    jensenPolynomial D.radius j (D.acceleratedRadius j) = 0 :=
  D.accelerated_is_smaller_root j hj

/-- Jensen's accelerated interval contains the target eigenvalue. -/
theorem target_mem_accelerated_interval (j : ℕ) (hj : 3 ≤ j) :
    InClosedInterval
      (D.shift - D.acceleratedRadius j)
      (D.shift + D.acceleratedRadius j)
      D.targetEigenvalue :=
  mem_centered_interval_of_abs_sub_le (D.accelerated_bounds_target j hj)

/-- The accelerated interval is no wider than the unaccelerated interval. -/
theorem accelerated_radius_le_radius (j : ℕ) (hj : 3 ≤ j) :
    D.acceleratedRadius j ≤ D.radius j :=
  D.accelerated_le_unaccelerated j hj

/-- If strict improvement is supplied, the accelerated interval is strictly narrower. -/
theorem accelerated_interval_strictly_narrows
    (j : ℕ) (_hj : 3 ≤ j)
    (hstrict : D.acceleratedRadius j < D.radius j) :
    D.acceleratedRadius j < D.radius j :=
  hstrict

end JensenAcceleratedInclusionData

end

end InfoGeometry.Canonical.JensenInverseIterationInclusion
