/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornKLProjection

/-!
# Ordinary relative entropy and the generalized-KL Sinkhorn objective

The mass correction is explicit. On a fixed marginal constraint set it is
constant, so both conventions have exactly the same minimizer. The ordinary
relative entropy formula also satisfies the Pythagorean identity.
-/
noncomputable section
open scoped BigOperators
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Exact relation between the two finite entropy conventions. -/
theorem matrixKL_eq_sum_logRatio (P Q : TransportPlan I J) :
    matrixKL P Q = (∑ i, ∑ j, P i j * Real.log (P i j / Q i j)) -
      (∑ i, ∑ j, P i j) + ∑ i, ∑ j, Q i j := by
  unfold matrixKL scalarKLDivergence
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The ordinary log-ratio relative entropy has the same exact Pythagorean law. -/
theorem relativeEntropy_pythagorean_of_scaling (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    (∑ i, ∑ j, P i j * Real.log (P i j / K i j)) =
      (∑ i, ∑ j, P i j * Real.log (P i j / (u i * K i j * v j))) +
      ∑ i, ∑ j, (u i * K i j * v j) * Real.log ((u i * K i j * v j) / K i j) := by
  have h := matrixKL_pythagorean_of_scaling P K u v hK hu hv hr hc
  simp only [matrixKL_eq_sum_logRatio] at h
  linarith

/-- The generalized-KL mass correction is constant on the marginal constraint set. -/
theorem relativeEntropy_scaling_minimizes (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hK : ∀ i j, 0 < K i j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    (∑ i, ∑ j, (u i * K i j * v j) * Real.log ((u i * K i j * v j) / K i j)) ≤
      ∑ i, ∑ j, P i j * Real.log (P i j / K i j) := by
  have hm : (∑ i, ∑ j, P i j) = ∑ i, ∑ j, u i * K i j * v j := by
    exact Finset.sum_congr rfl fun i _ => hr i
  have h := matrixKL_scaling_minimizes P K u v hP hK hu hv hr hc
  simp only [matrixKL_eq_sum_logRatio] at h
  rw [hm] at h
  linarith

/-- Ordinary relative entropy has the same strict equality case on fixed marginals. -/
theorem relativeEntropy_scaling_eq_iff (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hK : ∀ i j, 0 < K i j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    (∑ i, ∑ j, P i j * Real.log (P i j / K i j)) =
      (∑ i, ∑ j, (u i * K i j * v j) * Real.log ((u i * K i j * v j) / K i j)) ↔
      P = (fun i j => u i * K i j * v j) := by
  have hm : (∑ i, ∑ j, P i j) = ∑ i, ∑ j, u i * K i j * v j := by
    exact Finset.sum_congr rfl fun i _ => hr i
  have hg := matrixKL_scaling_eq_iff P K u v hP hK hu hv hr hc
  simp only [matrixKL_eq_sum_logRatio] at hg
  rw [hm] at hg
  constructor
  · intro he
    apply hg.1
    rw [he]
  · intro he
    subst P
    rfl

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
