/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility
import InfoGeometry.Canonical.KreinSpinConnectionObstruction

/-! The existing matrix commutator criterion is exactly the failure of its
ordinary self-adjoint operator to remain self-adjoint for the invertible
weight. This is a finite algebraic statement, not a manifold connection. -/

noncomputable section
namespace InfoGeometry.Canonical

theorem kreinMetric_mul_neg (mu : ℝ) :
    kreinMetric mu * kreinMetric (-mu) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinMetric, Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

def spinWeightUnit (mu : ℝ) : RealBlock2ˣ where
  val := kreinMetric mu
  inv := kreinMetric (-mu)
  val_inv := kreinMetric_mul_neg mu
  inv_val := by simpa only [neg_neg] using kreinMetric_mul_neg (-mu)

theorem spinConnection_selfAdjoint (u : ℝ) :
    star (spinConnection u) = spinConnection u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinConnection, Matrix.star_apply]

/-- The original obstruction is exactly weighted-adjoint incompatibility. -/
theorem spin_weighted_adjoint_eq_iff (u mu : ℝ) :
    OperatorAlgebra.WeightedAdjointCompatibility.adjoint (spinWeightUnit mu)
      (spinConnection u) = spinConnection u ↔ connectionMetricObstruction u mu = 0 := by
  rw [OperatorAlgebra.WeightedAdjointCompatibility.adjoint_eq_self_iff_of_selfAdjoint
    _ _ (spinConnection_selfAdjoint u)]
  change spinConnection u * kreinMetric mu = kreinMetric mu * spinConnection u ↔
    spinConnection u * kreinMetric mu - kreinMetric mu * spinConnection u = 0
  exact sub_eq_zero.symm

theorem spin_weighted_adjoint_eq_iff_mu_zero (u mu : ℝ) (hu : u ≠ 0) :
    OperatorAlgebra.WeightedAdjointCompatibility.adjoint (spinWeightUnit mu)
      (spinConnection u) = spinConnection u ↔ mu = 0 := by
  rw [spin_weighted_adjoint_eq_iff, compatibility_iff_mu_zero u mu hu]

end InfoGeometry.Canonical
end noncomputable section
