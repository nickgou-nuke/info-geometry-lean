import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- The conformal metric density is exactly the squared length of the
real planar differential, rather than an independently chosen coefficient. -/
theorem planeNormSq_dPhiCoeff_eq_metricDensity (x y : ℝ) :
    planeNormSq (dPhiCoeff x y) =
      BipolarApolloniusReflectionMetric.metricDensity ⟨x, y⟩ := by
  unfold BipolarApolloniusReflectionMetric.metricDensity
  rw [dlog01_eq_dPhiCoeff]
  simp [planeNormSq, planeDot, Complex.normSq_apply]

/-- The negative-gradient channel has the same conformal density. -/
theorem metricFlow_normSq_eq_metricDensity (x y : ℝ) :
    planeNormSq (metricFlow x y) =
      BipolarApolloniusReflectionMetric.metricDensity ⟨x, y⟩ := by
  rw [← planeNormSq_dPhiCoeff_eq_metricDensity]
  simp [metricFlow, planeNormSq, planeDot]

/-- Orthogonality makes the squared speed of the mixed field a sum of squares. -/
theorem mixedFlow_normSq (x y a b : ℝ) :
    planeNormSq (a • metricFlow x y + b • hamiltonianFlow x y) =
      (a ^ 2 + b ^ 2) * BipolarApolloniusReflectionMetric.metricDensity ⟨x, y⟩ := by
  rw [← planeNormSq_dPhiCoeff_eq_metricDensity]
  simp [planeNormSq, planeDot, metricFlow, hamiltonianFlow, hodgeRotate]
  ring

/-- On the punctured domain the two orthogonal directions cannot cancel. -/
theorem mixedFlow_eq_zero_iff {x y a b : ℝ}
    (hs : (⟨x, y⟩ : ℂ) ∈ BipolarCrossRatioLog.punctured01) :
    a • metricFlow x y + b • hamiltonianFlow x y = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hn := mixedFlow_normSq x y a b
    rw [h] at hn
    simp only [planeNormSq, planeDot, Pi.zero_apply, mul_zero, add_zero] at hn
    have hp := BipolarLocalConformalCoordinate.metricDensity_pos hs
    have hab : a ^ 2 + b ^ 2 = 0 :=
      (mul_eq_zero.mp hn.symm).resolve_right (ne_of_gt hp)
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · rintro ⟨rfl, rfl⟩
    simp

/-- Evaluation on the negative-gradient direction gives the negative metric
density. The curve here is the affine tangent line, not an assumed ODE solution. -/
theorem hasDerivAt_phiXY_metric_direction {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0) (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt
      (fun t => BipolarBoundaryTrace.phiXY
        (x + t * metricFlow x y 0) (y + t * metricFlow x y 1))
      (-BipolarApolloniusReflectionMetric.metricDensity ⟨x, y⟩) 0 := by
  have h := hasDerivAt_phiXY_line h0 h1 (metricFlow x y 0) (metricFlow x y 1)
  rw [← planeNormSq_dPhiCoeff_eq_metricDensity]
  convert h using 1; simp [planeNormSq, planeDot, metricFlow]; ring

/-- The Hodge-rotated direction is tangent to the potential level set,
expressed as an actual directional derivative. -/
theorem hasDerivAt_phiXY_hamiltonian_direction {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0) (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt
      (fun t => BipolarBoundaryTrace.phiXY
        (x + t * hamiltonianFlow x y 0) (y + t * hamiltonianFlow x y 1))
      0 0 := by
  have h := hasDerivAt_phiXY_line h0 h1
    (hamiltonianFlow x y 0) (hamiltonianFlow x y 1)
  convert h using 1; simp [hamiltonianFlow, hodgeRotate]; ring

/-- A curve satisfying the negative-gradient equation has the predicted
potential rate. This theorem does not assume or assert existence of solutions. -/
theorem hasDerivAt_phiXY_metric_curve {f g : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivAt f (metricFlow (f t) (g t) 0) t)
    (hg : HasDerivAt g (metricFlow (f t) (g t) 1) t)
    (h0 : f t ^ 2 + g t ^ 2 ≠ 0)
    (h1 : (f t - 1) ^ 2 + g t ^ 2 ≠ 0) :
    HasDerivAt (fun a => BipolarBoundaryTrace.phiXY (f a) (g a))
      (-BipolarApolloniusReflectionMetric.metricDensity ⟨f t, g t⟩) t := by
  have h := BipolarBoundaryTrace.hasDerivAt_phiXY_comp hf hg h0 h1
  rw [← planeNormSq_dPhiCoeff_eq_metricDensity]
  convert h using 1 <;> simp [planeNormSq, planeDot, metricFlow, dPhiCoeff] <;> ring

/-- The rotated component contributes zero to the potential rate of a mixed
trajectory; only the negative-gradient coefficient remains. -/
theorem hasDerivAt_phiXY_mixed_curve {f g : ℝ → ℝ} {t a b : ℝ}
    (hf : HasDerivAt f
      (a * metricFlow (f t) (g t) 0 + b * hamiltonianFlow (f t) (g t) 0) t)
    (hg : HasDerivAt g
      (a * metricFlow (f t) (g t) 1 + b * hamiltonianFlow (f t) (g t) 1) t)
    (h0 : f t ^ 2 + g t ^ 2 ≠ 0)
    (h1 : (f t - 1) ^ 2 + g t ^ 2 ≠ 0) :
    HasDerivAt (fun s => BipolarBoundaryTrace.phiXY (f s) (g s))
      (-a * BipolarApolloniusReflectionMetric.metricDensity ⟨f t, g t⟩) t := by
  have h := BipolarBoundaryTrace.hasDerivAt_phiXY_comp hf hg h0 h1
  rw [← planeNormSq_dPhiCoeff_eq_metricDensity]
  convert h using 1
  simp [planeNormSq, planeDot, metricFlow, hamiltonianFlow, hodgeRotate, dPhiCoeff]
  ring

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
  · unfold metricFlow dPhiCoeff
    norm_num
    have hpos : 0 < (1 / 4 : ℝ) + y ^ 2 := by
      nlinarith [sq_nonneg y]
    field_simp [ne_of_gt hpos]
    ring
  · unfold metricFlow dPhiCoeff
    norm_num

/-- On the bisector the Hamiltonian/Hodge channel is purely tangential. -/
theorem hamiltonianFlow_half (y : ℝ) :
    hamiltonianFlow (1 / 2) y =
      ![0, 1 / ((1 / 4 : ℝ) + y ^ 2)] := by
  rw [hamiltonianFlow_eq_dPsiCoeff]
  ext i
  fin_cases i
  · unfold dPsiCoeff
    norm_num
    ring
  · unfold dPsiCoeff
    norm_num
    have hpos : 0 < (1 / 4 : ℝ) + y ^ 2 := by
      nlinarith [sq_nonneg y]
    field_simp [ne_of_gt hpos]
    ring

/-- The normal metric channel does not vanish on the bisector. -/
theorem metricFlow_half_ne_zero (y : ℝ) : metricFlow (1 / 2) y ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [metricFlow_half] at h0
  have hvanish : 1 / ((1 / 4 : ℝ) + y ^ 2) = 0 := by
    have hzero : -(1 / ((1 / 4 : ℝ) + y ^ 2)) = 0 := by
      simpa using h0
    exact neg_eq_zero.mp hzero
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
