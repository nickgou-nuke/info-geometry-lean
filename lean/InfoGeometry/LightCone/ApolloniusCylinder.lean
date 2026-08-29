/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.LightCone.ApolloniusCylinder

open Matrix Real

noncomputable section

/-!
# Light-Cone Coordinates and Metric Factorization on the Apollonian Cylinder

This module formalizes the transformation between the rapidity-angle coordinates
$(\chi, \theta) \in \mathbb{R} \times S^1$ and the null light-cone coordinates $(u, v)$:

  $$u = \chi + \theta$$
  $$v = \chi - \theta$$

1. **Inverse Coordinate Transformation**:
   $$\chi = \frac{u + v}{2}, \qquad \theta = \frac{u - v}{2}$$

2. **Metric Factorization ($ds^2 = du \cdot dv$)**:
   The flat pseudo-Riemannian metric in rapidity-angle coordinates:
     $$ds^2 = d\chi^2 - d\theta^2$$
   factors identically into:
     $$ds^2 = \left(\frac{du + dv}{2}\right)^2 - \left(\frac{du - dv}{2}\right)^2 = du \cdot dv$$

3. **Jacobian Transformation Matrix**:
   $$J = \frac{\partial(\chi, \theta)}{\partial(u, v)} = \begin{pmatrix} 1/2 & 1/2 \\ 1/2 & -1/2 \end{pmatrix}$$
   with $\det(J) = -1/2 \neq 0$.

4. **Symplectic 2-Form in Light-Cone Basis**:
   $$\Omega = d\chi \wedge d\theta = -\frac{1}{2} du \wedge dv$$

5. **Chiral Decoupling of Vector Fields**:
   - Left-moving null vector: $\partial_u = \frac{1}{2}(\partial_\chi + \partial_\theta)$
   - Right-moving null vector: $\partial_v = \frac{1}{2}(\partial_\chi - \partial_\theta)$
   with $g(\partial_u, \partial_u) = 0$, $g(\partial_v, \partial_v) = 0$, and $g(\partial_u, \partial_v) = \frac{1}{2}$.
-/

/-- Light-cone forward map from rapidity-angle (χ, θ) to (u, v). -/
def toLightCone (χ θ : ℝ) : ℝ × ℝ :=
  (χ + θ, χ - θ)

/-- Light-cone inverse map from (u, v) back to (χ, θ). -/
def fromLightCone (u v : ℝ) : ℝ × ℝ :=
  ((u + v) / 2, (u - v) / 2)

/-- The quadratic metric interval in rapidity-angle coordinates: ds²(dχ, dθ) = dχ² - dθ². -/
def metricIntervalRapidityAngle (dχ dθ : ℝ) : ℝ :=
  dχ ^ 2 - dθ ^ 2

/-- The quadratic metric interval in light-cone coordinates: ds²(du, dv) = du * dv. -/
def metricIntervalLightCone (du dv : ℝ) : ℝ :=
  du * dv

/-- Jacobian transformation matrix from (u, v) to (χ, θ). -/
def jacobianLightConeToRapidity : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1 / 2, 1 / 2],
    ![1 / 2, -1 / 2]]

/-- The off-diagonal light-cone metric tensor g_LC = [[0, 1/2], [1/2, 0]]. -/
def lightConeMetricTensor : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1 / 2],
    ![1 / 2, 0]]

/-!
### 1. Inversion and Coordinate Round-Trips
-/

/-- 🏆 THEOREM 1 (Inverse Coordinate Transformation Identity):
    fromLightCone(u, v) accurately inverts toLightCone(χ, θ). -/
theorem lightcone_roundtrip (χ θ : ℝ) :
    fromLightCone (χ + θ) (χ - θ) = (χ, θ) := by
  unfold fromLightCone
  ext <;> ring

/-- 🏆 THEOREM 2 (Forward Coordinate Transformation Identity):
    toLightCone(χ, θ) accurately inverts fromLightCone(u, v). -/
theorem lightcone_forward_roundtrip (u v : ℝ) :
    toLightCone ((u + v) / 2) ((u - v) / 2) = (u, v) := by
  unfold toLightCone
  ext <;> ring

/-!
### 2. Exact Metric Factorization ds² = du · dv
-/

/-- 🏆 THEOREM 3 (Fundamental Metric Factorization ds² = dχ² - dθ² = du · dv):
    Substituting dχ = (du + dv)/2 and dθ = (du - dv)/2 into dχ² - dθ² yields exactly du * dv. -/
theorem metric_factorization_identity (du dv : ℝ) :
    metricIntervalRapidityAngle ((du + dv) / 2) ((du - dv) / 2) =
    metricIntervalLightCone du dv := by
  unfold metricIntervalRapidityAngle metricIntervalLightCone
  ring

/-- 🏆 THEOREM 4 (Reverse Metric Factorization du · dv = dχ² - dθ²):
    Evaluating (dχ + dθ)(dχ - dθ) reproduces the pseudo-Riemannian interval dχ² - dθ². -/
theorem metric_factorization_reverse (dχ dθ : ℝ) :
    metricIntervalLightCone (dχ + dθ) (dχ - dθ) =
    metricIntervalRapidityAngle dχ dθ := by
  unfold metricIntervalLightCone metricIntervalRapidityAngle
  ring

/-!
### 3. Jacobian Determinant and Light-Cone Tensor Form
-/

/-- 🏆 THEOREM 5 (Jacobian Determinant Non-Degeneracy):
    The transformation has constant non-zero Jacobian determinant det(J) = -1/2. -/
theorem jacobian_lightcone_det :
    jacobianLightConeToRapidity.det = -1 / 2 := by
  unfold jacobianLightConeToRapidity
  rw [Matrix.det_fin_two]
  simp only [cons_val_zero, cons_val_one]
  ring

/-- 🏆 THEOREM 6 (Light-Cone Metric Tensor Determinant):
    The determinant of the light-cone metric tensor is det(g_LC) = -1/4. -/
theorem lightcone_metric_det :
    lightConeMetricTensor.det = -1 / 4 := by
  unfold lightConeMetricTensor
  rw [Matrix.det_fin_two]
  simp only [cons_val_zero, cons_val_one]
  ring

/-- 🏆 THEOREM 7 (Null Geodesic Rays / Isotropic Vectors):
    The diagonal components of the light-cone metric vanish: g(∂_u, ∂_u) = 0 and g(∂_v, ∂_v) = 0. -/
theorem lightcone_null_diagonals :
    lightConeMetricTensor 0 0 = 0 ∧
    lightConeMetricTensor 1 1 = 0 ∧
    lightConeMetricTensor 0 1 = 1 / 2 ∧
    lightConeMetricTensor 1 0 = 1 / 2 := by
  unfold lightConeMetricTensor
  refine ⟨rfl, rfl, rfl, rfl⟩

/-!
### 4. Symplectic 2-Form in Light-Cone Coordinates
-/

/-- 🏆 THEOREM 8 (Symplectic Form Transformation: dχ ∧ dθ = - ½ du ∧ dv):
    The determinant of the coordinate differential wedge transforms by the factor of -1/2. -/
theorem symplectic_lightcone_wedge (du_1 du_2 dv_1 dv_2 : ℝ) :
    let dχ_1 := (du_1 + dv_1) / 2
    let dχ_2 := (du_2 + dv_2) / 2
    let dθ_1 := (du_1 - dv_1) / 2
    let dθ_2 := (du_2 - dv_2) / 2
    dχ_1 * dθ_2 - dχ_2 * dθ_1 = - (1 / 2) * (du_1 * dv_2 - du_2 * dv_1) := by
  intro dχ_1 dχ_2 dθ_1 dθ_2
  dsimp [dχ_1, dχ_2, dθ_1, dθ_2]
  ring

/-!
### 5. Grand Capstone: Light-Cone Geometry Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Complete formal verification of the light-cone coordinate bijection,
    exact algebraic metric factorization ds² = du · dv, non-degenerate Jacobian determinant,
    vanishing of null diagonal metric components, and canonical symplectic scaling -/
theorem grand_lightcone_factorization_synthesis
    (χ θ du dv : ℝ) :
    (fromLightCone (χ + θ) (χ - θ) = (χ, θ)) ∧
    (toLightCone ((du + dv) / 2) ((du - dv) / 2) = (du, dv)) ∧
    (metricIntervalRapidityAngle ((du + dv) / 2) ((du - dv) / 2) = metricIntervalLightCone du dv) ∧
    (metricIntervalLightCone (χ + θ) (χ - θ) = metricIntervalRapidityAngle χ θ) ∧
    (jacobianLightConeToRapidity.det = -1 / 2) ∧
    (lightConeMetricTensor 0 0 = 0 ∧ lightConeMetricTensor 1 1 = 0) :=
  ⟨lightcone_roundtrip χ θ,
   lightcone_forward_roundtrip du dv,
   metric_factorization_identity du dv,
   metric_factorization_reverse χ θ,
   jacobian_lightcone_det,
   ⟨lightcone_null_diagonals.1, lightcone_null_diagonals.2.1⟩⟩

end

end InfoGeometry.LightCone.ApolloniusCylinder
