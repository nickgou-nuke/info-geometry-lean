import InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Section31UnifiedMatrixDynamics

/-!
# Section 32 repaired: quaternionic emergent-spacetime finite socket

The source text states an axiomatic quaternionic-emergent-spacetime program.  In
this repository we keep only the finite algebra that the kernel can check:

* the existing Pauli owner supplies the matrix basis, determinant/Minkowski
  readout, Bloch density determinant, Bloch precession, and the corrected
  quaternion sign convention;
* this file adds the conformal/Bloch-radius spacetime parametrization
  `t · (I + r n·σ)`, its density-matrix readback, determinant formula, null
  boundary certificate, scalar conformal covariance, and a finite Lüders
  projection numerator identity.

The informal claims that time, gravity, torsion, Einstein equations,
entanglement connections, black-hole information, or cosmological dynamics
*emerge* from the condensate are not asserted as theorems here.
-/

noncomputable section

namespace InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime

open Matrix Complex
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section31UnifiedMatrixDynamics

/-- Section 32 repaired spacetime point `t · (I + r n·σ)` in the Pauli carrier. -/
def blochSpacetimePoint (t r n1 n2 n3 : ℂ) : Mat2 :=
  pauliPointRaw t (t * r * n1) (t * r * n2) (t * r * n3)

/-- The associated trace-one Bloch density at radius `r`. -/
def blochDensityAtRadius (r n1 n2 n3 : ℂ) : Mat2 :=
  densityMatrix (r * n1) (r * n2) (r * n3)

/-- The Section 32 point is exactly `2t` times the associated density matrix. -/
theorem blochSpacetimePoint_eq_two_t_smul_density (t r n1 n2 n3 : ℂ) :
    blochSpacetimePoint t r n1 n2 n3 =
      (2 * t) • blochDensityAtRadius r n1 n2 n3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochSpacetimePoint, blochDensityAtRadius, pauliPointRaw, densityMatrix]
  all_goals ring

/-- Determinant of the repaired conformal/Bloch-radius spacetime point. -/
theorem blochSpacetimePoint_det (t r n1 n2 n3 : ℂ) :
    (blochSpacetimePoint t r n1 n2 n3).det =
      t ^ 2 * (1 - r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2)) := by
  rw [blochSpacetimePoint, pauliPointRaw_det]
  ring

/-- Minkowski readout of the repaired Section 32 point. -/
theorem blochSpacetimePoint_minkowski_readout (t r n1 n2 n3 : ℂ) :
    - (blochSpacetimePoint t r n1 n2 n3).det =
      -t ^ 2 + (t * r * n1) ^ 2 + (t * r * n2) ^ 2 + (t * r * n3) ^ 2 := by
  rw [blochSpacetimePoint, pauliPointRaw_det]
  ring

/-- Unit direction and boundary radius give the finite null determinant certificate. -/
theorem blochSpacetimePoint_det_zero_of_unit_boundary (t r n1 n2 n3 : ℂ)
    (hunit : n1 ^ 2 + n2 ^ 2 + n3 ^ 2 = 1) (hr : r ^ 2 = 1) :
    (blochSpacetimePoint t r n1 n2 n3).det = 0 := by
  rw [blochSpacetimePoint_det, hunit, hr]
  ring

/-- Scalar conformal covariance: scaling `t` scales the Pauli point. -/
theorem blochSpacetimePoint_scale_time (lam t r n1 n2 n3 : ℂ) :
    blochSpacetimePoint (lam * t) r n1 n2 n3 =
      lam • blochSpacetimePoint t r n1 n2 n3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochSpacetimePoint, pauliPointRaw]
  all_goals ring

/-- The determinant scales quadratically under the finite conformal scaling. -/
theorem blochSpacetimePoint_det_scale_time (lam t r n1 n2 n3 : ℂ) :
    (blochSpacetimePoint (lam * t) r n1 n2 n3).det =
      lam ^ 2 * (blochSpacetimePoint t r n1 n2 n3).det := by
  rw [blochSpacetimePoint_det, blochSpacetimePoint_det]
  ring

/-- Finite Lüders numerator identity: a projector supports its own measurement numerator. -/
theorem luders_numerator_supported_by_projector (P rho : Mat2)
    (hP : P * P = P) :
    P * (P * rho * P) * P = P * rho * P := by
  calc
    P * (P * rho * P) * P = (P * P) * rho * (P * P) := by simp [mul_assoc]
    _ = P * rho * P := by simp [hP]

/-- The repaired Section 32 packet: quaternion sign correction, null boundary, and precession. -/
theorem repaired_section32_quaternionic_spacetime_packet
    (t r n1 n2 n3 ω1 ω2 ω3 : ℂ)
    (hunit : n1 ^ 2 + n2 ^ 2 + n3 ^ 2 = 1) (hr : r ^ 2 = 1) :
    (Complex.I • σ1) * (Complex.I • σ2) = -(Complex.I • σ3) ∧
    (blochSpacetimePoint t r n1 n2 n3).det = 0 ∧
    vonNeumannRHS ω1 ω2 ω3 (r * n1) (r * n2) (r * n3) =
      (1 / 2 : ℂ) •
        (blochCross1 ω1 ω2 ω3 (r * n1) (r * n2) (r * n3) • σ1 +
          blochCross2 ω1 ω2 ω3 (r * n1) (r * n2) (r * n3) • σ2 +
          blochCross3 ω1 ω2 ω3 (r * n1) (r * n2) (r * n3) • σ3) := by
  exact ⟨quaternion_literal_i_j_sign_obstruction,
    blochSpacetimePoint_det_zero_of_unit_boundary t r n1 n2 n3 hunit hr,
    vonNeumannRHS_eq_bloch_precession ω1 ω2 ω3 (r * n1) (r * n2) (r * n3)⟩

end InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime

end noncomputable section
