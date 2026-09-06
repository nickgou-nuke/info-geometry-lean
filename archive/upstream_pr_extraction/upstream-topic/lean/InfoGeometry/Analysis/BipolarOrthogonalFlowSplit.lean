import InfoGeometry.Analysis.BipolarPlanarHodgePair
import Mathlib.Tactic

/-!
# Orthogonal planar flow split for the bipolar potential

The informal metriplectic discussion mixed the harmonic-conjugate potential with
the Hamiltonian generator. Pointwise on the Euclidean plane the clean algebra is
simpler: for one scalar potential `Phi`, the gradient channel and its Hodge-rotated
channel are

`G = -grad Phi`,    `H = J grad Phi`.

These two vectors are orthogonal and have equal Euclidean squared norm. Because
`dPsi = J dPhi`, using `Psi` as a Hamiltonian would rotate once more and recover
`-dPhi`; it is not an independent third channel.

No entropy-production, Poisson-Jacobi, or global dissipative dynamics theorem is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarOrthogonalFlowSplit

open InfoGeometry.Analysis.BipolarPlanarHodgePair

/-- Euclidean pairing of planar coefficient vectors. -/
def planeDot (u v : PlaneCovector) : ℝ := u 0 * v 0 + u 1 * v 1

/-- Euclidean squared norm of a planar coefficient vector. -/
def planeNormSq (u : PlaneCovector) : ℝ := planeDot u u

/-- Negative gradient channel. -/
def metricFlow (x y : ℝ) : PlaneCovector := -dPhiCoeff x y

/-- Hodge-rotated gradient channel. -/
def hamiltonianFlow (x y : ℝ) : PlaneCovector := hodgeRotate (dPhiCoeff x y)

/-- The Hamiltonian channel is exactly the angular differential coefficient. -/
theorem hamiltonianFlow_eq_dPsiCoeff (x y : ℝ) :
    hamiltonianFlow x y = dPsiCoeff x y := by
  rw [hamiltonianFlow, dPsiCoeff_eq_hodgeRotate_dPhiCoeff]

/-- Gradient and Hodge-rotated gradient are pointwise orthogonal. -/
theorem metric_hamiltonian_orthogonal (x y : ℝ) :
    planeDot (metricFlow x y) (hamiltonianFlow x y) = 0 := by
  simp [planeDot, metricFlow, hamiltonianFlow, hodgeRotate]
  ring

/-- Hodge rotation preserves the Euclidean squared norm. -/
theorem planeNormSq_hodgeRotate (v : PlaneCovector) :
    planeNormSq (hodgeRotate v) = planeNormSq v := by
  simp [planeNormSq, planeDot, hodgeRotate]
  ring

/-- The two channels have equal pointwise squared norm. -/
theorem metric_hamiltonian_equal_normSq (x y : ℝ) :
    planeNormSq (metricFlow x y) = planeNormSq (hamiltonianFlow x y) := by
  rw [metricFlow, hamiltonianFlow, planeNormSq_hodgeRotate]
  simp [planeNormSq, planeDot]

/-- Rotating the angular differential once more returns minus the gradient. -/
theorem rotate_angular_eq_metric_generator (x y : ℝ) :
    hodgeRotate (dPsiCoeff x y) = metricFlow x y := by
  rw [hodgeRotate_dPsiCoeff]
  rfl

/-- On the bisector the metric channel is purely normal and nonzero. -/
theorem metricFlow_half (y : ℝ) :
    metricFlow (1 / 2) y =
      ![-(1 / ((1 / 4 : ℝ) + y ^ 2)), 0] := by
  ext i
  fin_cases i
  · simp [metricFlow, dPhiCoeff_half_normal]
  · simp [metricFlow, dPhiCoeff_half_tangent_zero]

/-- On the bisector the Hamiltonian/Hodge channel is purely tangential. -/
theorem hamiltonianFlow_half (y : ℝ) :
    hamiltonianFlow (1 / 2) y =
      ![0, 1 / ((1 / 4 : ℝ) + y ^ 2)] := by
  rw [hamiltonianFlow_eq_dPsiCoeff]
  ext i
  fin_cases i
  · simp [dPsiCoeff_half_normal_zero]
  · simp [dPsiCoeff_half_tangent]

/-- The normal metric channel does not vanish on the bisector. -/
theorem metricFlow_half_ne_zero (y : ℝ) : metricFlow (1 / 2) y ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [metricFlow_half] at h0
  have hvanish : 1 / ((1 / 4 : ℝ) + y ^ 2) = 0 := by
    simpa using neg_eq_zero.mp (by simpa using h0)
  have hpos : 0 < (1 / 4 : ℝ) + y ^ 2 := by
    nlinarith [sq_nonneg y]
  exact (one_div_ne_zero (ne_of_gt hpos)) hvanish

/-- Compact corrected flow packet. -/
theorem orthogonal_flow_packet (x y : ℝ) :
    hamiltonianFlow x y = dPsiCoeff x y ∧
      planeDot (metricFlow x y) (hamiltonianFlow x y) = 0 ∧
      planeNormSq (metricFlow x y) = planeNormSq (hamiltonianFlow x y) := by
  exact ⟨hamiltonianFlow_eq_dPsiCoeff x y,
    metric_hamiltonian_orthogonal x y,
    metric_hamiltonian_equal_normSq x y⟩

end InfoGeometry.Analysis.BipolarOrthogonalFlowSplit
