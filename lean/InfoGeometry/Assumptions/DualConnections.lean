import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped BigOperators

/-!
# Assumptions.DualConnections

Assumption-backed interface for dual-connection geometry drafts extracted from
the historical `InfoGeometry/New.lean`.
-/

namespace InfoGeometry.Assumptions.DualConnections

variable {Θ α : Type*} [Fintype α]

/--
Fisher-metric compatibility marker:
each fiber is a normalized finite probability vector.
-/
def fisherMetric (p : Θ → InfoGeometry.FinProb α) : Prop :=
  ∀ θ : Θ, ∑ a : α, p θ a = 1

/--
Amari-Chentsov nonnegativity surrogate:
nonnegativity of the quadratic probability moment on each fiber.
-/
def amariChentsovTensor (p : Θ → InfoGeometry.FinProb α) : Prop :=
  ∀ θ : Θ, 0 ≤ ∑ a : α, (p θ a) ^ (2 : ℕ)

/-- `α`-connection scaffold requiring Fisher and Chentsov compatibility. -/
def alphaConnection (p : Θ → InfoGeometry.FinProb α) (_αc : ℝ) : Prop :=
  fisherMetric p ∧ amariChentsovTensor p

/--
`±α` duality in this scaffold:
the connection side conditions are independent of the sign of `α`.
-/
theorem alpha_duality (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) :
  alphaConnection p αc ↔ alphaConnection p (-αc)
    := by
  simp [alphaConnection]

/-- Finite-probability fibers satisfy the Fisher normalization marker. -/
theorem fisherMetric_of_finProb (p : Θ → InfoGeometry.FinProb α) :
    fisherMetric p := by
  intro θ
  classical
  simpa [fisherMetric, tsum_fintype] using (p θ).tsum_coe

/-- Finite-probability fibers satisfy the Chentsov quadratic nonnegativity marker. -/
theorem amariChentsovTensor_of_finProb (p : Θ → InfoGeometry.FinProb α) :
    amariChentsovTensor p := by
  intro θ
  refine Finset.sum_nonneg ?_
  intro a ha
  exact sq_nonneg (p θ a)

/--
Compatibility bridge name preserved:
Fisher-normalized fibers imply the quadratic Chentsov nonnegativity marker.
-/
theorem fisher_metric_eq_hessian_KL (p : Θ → InfoGeometry.FinProb α) :
    fisherMetric p → amariChentsovTensor p := by
  intro _hf
  exact amariChentsovTensor_of_finProb p

end InfoGeometry.Assumptions.DualConnections
