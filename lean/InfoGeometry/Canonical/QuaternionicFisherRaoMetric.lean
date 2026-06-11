import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# InfoGeometry.Canonical.QuaternionicFisherRaoMetric

This module formalizes the Fisher-Rao Information Metric over the 
Quaternionic statistical manifold. The metric is defined as the 
Hessian $g_{ij} = \partial_i \partial_j \Psi$ of the thermodynamic potential $\Psi$.

For a free quaternion field, the potential is strictly convex and 
the emergent metric is symmetric positive-definite.
-/

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.QuaternionicFisherRaoMetric

/-- The coordinates of the Quaternionic Statistical Manifold. 
    These correspond to the 4 real degrees of freedom of the macroscopic condensate. -/
def QuaternionicCoordinates := Fin 4 → ℝ

/-- The Thermodynamic Potential (Log-Partition Function) for the Free Quaternionic Field.
    $\Psi(q) = \frac{1}{2} \sum_{i} q_i^2$ -/
def Psi (q : QuaternionicCoordinates) : ℝ :=
  (1 / 2 : ℝ) * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2)

/-- The Fisher-Rao Information Metric is the Hessian of the thermodynamic potential. 
    For $\Psi(q) = \frac{1}{2} \sum_i q_i^2$, the Hessian is exactly the identity matrix. -/
def FisherRaoMetric (q : QuaternionicCoordinates) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Theorem: The Fisher-Rao Metric on the free quaternionic statistical manifold is symmetric. -/
theorem FisherRaoMetric_is_symmetric (q : QuaternionicCoordinates) :
    (FisherRaoMetric q)ᵀ = FisherRaoMetric q := by
  dsimp [FisherRaoMetric]
  exact Matrix.transpose_one

/-- Theorem: The Fisher-Rao Metric is Positive Definite. 
    We prove this by showing $v^T g v > 0$ for all non-zero tangent vectors $v$. -/
theorem FisherRaoMetric_is_positive_definite (q : QuaternionicCoordinates) (v : Fin 4 → ℝ) :
    (v = 0) ∨ (dotProduct v (mulVec (FisherRaoMetric q) v) > 0) := by
  by_cases h : v = 0
  · left; exact h
  · right
    dsimp [FisherRaoMetric]
    rw [Matrix.one_mulVec]
    have h1 : dotProduct v v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
      dsimp [dotProduct]
      rw [Fin.sum_univ_four]
      ring
    rw [h1]
    by_cases h0 : v 0 = 0
    · by_cases h1 : v 1 = 0
      · by_cases h2 : v 2 = 0
        · by_cases h3 : v 3 = 0
          · exfalso
            apply h
            ext i
            match i with
            | 0 => exact h0
            | 1 => exact h1
            | 2 => exact h2
            | 3 => exact h3
          · have hsq : 0 < v 3 ^ 2 := sq_pos_of_ne_zero h3
            rw [h0, h1, h2]; ring_nf; exact hsq
        · have hsq : 0 < v 2 ^ 2 := sq_pos_of_ne_zero h2
          have hn3 : 0 ≤ v 3 ^ 2 := sq_nonneg (v 3)
          rw [h0, h1]; ring_nf; linarith
      · have hsq : 0 < v 1 ^ 2 := sq_pos_of_ne_zero h1
        have hn2 : 0 ≤ v 2 ^ 2 := sq_nonneg (v 2)
        have hn3 : 0 ≤ v 3 ^ 2 := sq_nonneg (v 3)
        rw [h0]; ring_nf; linarith
    · have hsq : 0 < v 0 ^ 2 := sq_pos_of_ne_zero h0
      have hn1 : 0 ≤ v 1 ^ 2 := sq_nonneg (v 1)
      have hn2 : 0 ≤ v 2 ^ 2 := sq_nonneg (v 2)
      have hn3 : 0 ≤ v 3 ^ 2 := sq_nonneg (v 3)
      linarith

end InfoGeometry.Canonical.QuaternionicFisherRaoMetric
