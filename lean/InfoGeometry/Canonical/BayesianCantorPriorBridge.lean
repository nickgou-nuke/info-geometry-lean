import InfoGeometry.Basic
import InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/-!
# Bayesian Cantor Prior Bridge

Finite Bayesian readout on the repo's Cantor/Bratteli tape.

This file does one thing only:

* package a deterministic point prior on each finite bitword stage;
* prove that its cylinder expectation is exactly the existing Boolean
  evaluation on that stage;
* prove that this readout is compatible with the successor/pullback map.

No analytic Radon measure or KMS theorem is claimed here.  This is the finite
probability skeleton that the later state-layer can extend.
-/

noncomputable section

namespace BayesianCantorPriorBridge

open InfoGeometry
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge
open scoped BigOperators ENNReal

/-- Real-valued indicator of a set membership. -/
noncomputable def indicator {α : Type*} (A : Set α) (x : α) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

/-- Deterministic prior concentrated at a single finite bitword. -/
def pointPrior (n : ℕ) (w : BitWord n) : FinProb (BitWord n) :=
  PMF.pure w

@[simp] theorem pointPrior_apply (n : ℕ) (w u : BitWord n) :
    pointPrior n w u = if u = w then (1 : ℝ≥0∞) else 0 := by
  simp [pointPrior]

/-- The expectation of a cylinder indicator under a point prior is the
Boolean evaluation of that cylinder at the chosen word. -/
theorem pointPrior_expectation_cylinder
    (n : ℕ) (w : BitWord n) (A : FiniteBooleanAlgebra n) :
    InfoGeometry.expectation (pointPrior n w) (indicator A) = indicator A w := by
  classical
  unfold pointPrior InfoGeometry.expectation indicator
  rw [Fintype.sum_eq_single w]
  · simp [PMF.pure_apply]
  · intro x hne
    simp [PMF.pure_apply_of_ne (a := w) (a' := x) hne]

/-- A point prior reads the same cylinder value through the finite Stone evaluation. -/
theorem pointPrior_expectation_boolEvalAt
    (n : ℕ) (w : BitWord n) (A : FiniteBooleanAlgebra n) :
    InfoGeometry.expectation (pointPrior n w) (indicator A) =
      (if boolEvalAt n w A then (1 : ℝ) else 0) := by
  classical
  rw [pointPrior_expectation_cylinder]
  by_cases h : w ∈ A <;> simp [boolEvalAt, indicator, h]

/-- Successor compatibility of the point prior readout along prefix pullback. -/
theorem pointPrior_prefixPullback
    (x : CantorBoundary) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    InfoGeometry.expectation
        (pointPrior (n + 1) (boundaryPrefix (n + 1) x))
        (indicator (prefixPullback n A)) =
      InfoGeometry.expectation
        (pointPrior n (boundaryPrefix n x))
        (indicator A) := by
  simpa [indicator, pointPrior_expectation_boolEvalAt, cantorBooleanEvaluation] using
    congrArg (fun b : Bool => if b then (1 : ℝ) else 0)
      (cantorBooleanEvaluation_prefixPullback x n A)

end BayesianCantorPriorBridge
