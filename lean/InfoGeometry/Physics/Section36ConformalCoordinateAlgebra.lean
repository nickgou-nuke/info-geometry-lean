import InfoGeometry.Physics.Section35IntegratedConcepts
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Section 36 repaired: conformal-coordinate finite algebra

The source develops conformal coordinates, simplified Einstein/Dirac equations,
entropy-time dilation, complex symmetry parameters, Kähler structure, and chiral
arrow-of-time claims.  The continuum derivations are not theorem-safe as stated.

This repaired owner records only the finite algebraic core:

* conformal spatial coordinates `xᵢ = t r nᵢ` and their squared-norm law;
* unit-direction specialization, matching the Bloch determinant residual already
  proved in Section 35;
* a deliberately finite second-order approximation identity connecting the
  quadratic entropy defect `-r²/2` with the quadratic time-dilation defect
  `r²/2`;
* a finite Hamiltonian-asymmetry readout `H₁-H₂`, with exact zero iff the two
  finite Hamiltonian matrices agree.

No theorem is asserted about Jacobians, Einstein equations, Dirac equations,
actual von-Neumann entropy, Taylor remainders, Kähler manifolds, gauge/Lorentz
unification, electroweak physics, or an arrow of time.
-/

noncomputable section

namespace InfoGeometry.Physics.Section36ConformalCoordinateAlgebra

open Matrix Complex
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime
open InfoGeometry.Physics.Section35IntegratedConcepts

/-- Real three-vector used for finite conformal-coordinate algebra. -/
abbrev RVec3 := InfoGeometry.Algebra.FiniteSpin.Vec3R

/-- Squared Euclidean norm of a finite real direction vector. -/
def directionNormSq (n : RVec3) : ℝ :=
  n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2

/-- Spatial coordinates from conformal data: `xᵢ = t r nᵢ`. -/
def conformalSpatial (t r : ℝ) (n : RVec3) : RVec3 :=
  fun i => t * r * n i

/-- Squared Euclidean norm of finite spatial coordinates. -/
def spatialNormSq (x : RVec3) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

/-- The conformal spatial norm is `t² r² ‖n‖²`. -/
theorem spatialNormSq_conformalSpatial (t r : ℝ) (n : RVec3) :
    spatialNormSq (conformalSpatial t r n) =
      t ^ 2 * r ^ 2 * directionNormSq n := by
  simp [spatialNormSq, conformalSpatial, directionNormSq]
  ring

/-- For a unit direction, the conformal spatial norm is `t²r²`. -/
theorem spatialNormSq_conformalSpatial_unit (t r : ℝ) (n : RVec3)
    (hunit : directionNormSq n = 1) :
    spatialNormSq (conformalSpatial t r n) = t ^ 2 * r ^ 2 := by
  rw [spatialNormSq_conformalSpatial, hunit]
  ring

/-- Finite proper-time-squared residual `1-r²`, not an analytic square root. -/
def properTimeSqResidual (r : ℝ) : ℝ :=
  1 - r ^ 2

/-- With unit direction, the real spatial residual is `t²(1-r²)`. -/
theorem time_minus_space_residual_unit (t r : ℝ) (n : RVec3)
    (hunit : directionNormSq n = 1) :
    t ^ 2 - spatialNormSq (conformalSpatial t r n) =
      t ^ 2 * properTimeSqResidual r := by
  rw [spatialNormSq_conformalSpatial_unit t r n hunit]
  simp [properTimeSqResidual]
  ring

/-- Section 35 Bloch residual specialized to the `x`-axis direction. -/
theorem blochResidual_axis (r : ℂ) :
    blochResidual r 1 0 0 = 1 - r ^ 2 := by
  simp [blochResidual]

/-- Quadratic entropy defect from the source's second-order expansion. -/
def entropyQuadraticDefect (r : ℝ) : ℝ :=
  -r ^ 2 / 2

/-- Quadratic time-dilation defect `1 - (1-r²/2)`. -/
def timeDilationQuadraticDefect (r : ℝ) : ℝ :=
  1 - (1 - r ^ 2 / 2)

/-- The repaired second-order comparison: the two quadratic defects are negatives. -/
theorem entropyQuadraticDefect_eq_neg_timeDilationQuadraticDefect (r : ℝ) :
    entropyQuadraticDefect r = -timeDilationQuadraticDefect r := by
  simp [entropyQuadraticDefect, timeDilationQuadraticDefect]
  ring

/-- Finite Hamiltonian asymmetry readout `H₁-H₂`. -/
def hamiltonianAsymmetry (H1 H2 : Mat2) : Mat2 :=
  H1 - H2

/-- Zero finite Hamiltonian asymmetry is exactly equality of the two matrices. -/
theorem hamiltonianAsymmetry_zero_iff (H1 H2 : Mat2) :
    hamiltonianAsymmetry H1 H2 = 0 ↔ H1 = H2 := by
  unfold hamiltonianAsymmetry
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    rw [h]
    simp

/-- Equal Hamiltonian components have zero finite asymmetry. -/
theorem hamiltonianAsymmetry_self (H : Mat2) :
    hamiltonianAsymmetry H H = 0 := by
  simp [hamiltonianAsymmetry]

/-- Repaired Section 36 finite packet. -/
theorem repaired_section36_conformal_coordinate_packet
    (t r : ℝ) (n : RVec3) (H1 H2 : Mat2)
    (hunit : directionNormSq n = 1) :
    spatialNormSq (conformalSpatial t r n) = t ^ 2 * r ^ 2 ∧
    t ^ 2 - spatialNormSq (conformalSpatial t r n) =
      t ^ 2 * properTimeSqResidual r ∧
    entropyQuadraticDefect r = -timeDilationQuadraticDefect r ∧
    (hamiltonianAsymmetry H1 H2 = 0 ↔ H1 = H2) := by
  exact ⟨spatialNormSq_conformalSpatial_unit t r n hunit,
    time_minus_space_residual_unit t r n hunit,
    entropyQuadraticDefect_eq_neg_timeDilationQuadraticDefect r,
    hamiltonianAsymmetry_zero_iff H1 H2⟩

end InfoGeometry.Physics.Section36ConformalCoordinateAlgebra

end noncomputable section
