/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealMatrixGibbs
import InfoGeometry.Thermo.RealDensityRadialFlow

/-! # Constant Gibbs entropy on native real unitary orbits

The full real matrix carrier is the one used by the radial mixing owner.
Native real unitary conjugation is orthogonal conjugation.  Exponential
naturality and trace cyclicity give covariance of the entire Gibbs density,
not merely of a scalar surrogate.  The proved Massieu identity then gives
invariance of its actual density-weighted CFC entropy.

The final commutant lemmas preserve any specified internal real operator `J`.
They do not identify all real matrices with a complex state space, nor assume
commutation of an arbitrary thermodynamic variation with the exponent.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixGibbsOrbit

open SouriauHilbertSchmidtOnsager
open RealMatrixGibbs
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Mat" => MatrixSpace n

local instance : NormedAlgebra ℚ Mat := NormedAlgebra.restrictScalars ℚ ℝ Mat

/-- The native star-algebra automorphism preserves self-adjoint exponents. -/
theorem isSelfAdjoint_unitary_conjugate (U : unitary Mat) (K : Mat)
    (hK : IsSelfAdjoint K) :
    IsSelfAdjoint ((U : Mat) * K * star (U : Mat)) :=
  hK.map (Unitary.conjStarAlgAut ℝ Mat U)

/-- Naturality holds on the full matrix algebra without a commutation premise. -/
theorem exp_unitary_conjugate (U : unitary Mat) (K : Mat) :
    NormedSpace.exp ((U : Mat) * K * star (U : Mat)) =
      (U : Mat) * NormedSpace.exp K * star (U : Mat) := by
  let φ := Unitary.conjStarAlgAut ℝ Mat U
  have hφ : Continuous φ := by
    change Continuous (fun X : Mat => (U : Mat) * X * star (U : Mat))
    exact (continuous_const.mul continuous_id).mul continuous_const
  simpa only [φ, Unitary.conjStarAlgAut_apply] using
    (NormedSpace.map_exp φ hφ K).symm

theorem partition_unitary_conjugate (U : unitary Mat) (K : Mat) :
    partition ((U : Mat) * K * star (U : Mat)) = partition K := by
  simp only [partition, exp_unitary_conjugate,
    RealDensityRadialFlow.trace_unitary_conjugate]

theorem massieu_unitary_conjugate (U : unitary Mat) (K : Mat) :
    massieu ((U : Mat) * K * star (U : Mat)) = massieu K := by
  simp only [massieu, partition_unitary_conjugate]

/-- Covariance of the constructed normalized positive matrix. -/
theorem density_unitary_conjugate (U : unitary Mat) (K : Mat) :
    density ((U : Mat) * K * star (U : Mat)) =
      (U : Mat) * density K * star (U : Mat) := by
  simp only [density, partition_unitary_conjugate, exp_unitary_conjugate,
    smul_mul_assoc, mul_smul_comm]

/-- Transforming both the state exponent and observable preserves expectation. -/
theorem expectation_unitary_conjugate (U : unitary Mat) (K A : Mat) :
    expectation ((U : Mat) * K * star (U : Mat))
        ((U : Mat) * A * star (U : Mat)) = expectation K A := by
  have hmul :
      ((U : Mat) * density K * star (U : Mat)) *
          ((U : Mat) * A * star (U : Mat)) =
        (U : Mat) * (density K * A) * star (U : Mat) := by
    simpa only [Unitary.conjStarAlgAut_apply] using
      (map_mul (Unitary.conjStarAlgAut ℝ Mat U) (density K) A).symm
  simp only [expectation, density_unitary_conjugate, hmul,
    RealDensityRadialFlow.trace_unitary_conjugate]

/-- The actual CFC Gibbs entropy is constant along every real unitary orbit. -/
theorem entropy_unitary_conjugate [Nonempty (Fin n)]
    (U : unitary Mat) (K : Mat) (hK : IsSelfAdjoint K) :
    entropy ((U : Mat) * K * star (U : Mat)) = entropy K := by
  rw [entropy_eq_massieu_sub_expectation _
      (isSelfAdjoint_unitary_conjugate U K hK),
    entropy_eq_massieu_sub_expectation K hK,
    massieu_unitary_conjugate, expectation_unitary_conjugate]

/-- Functional calculus and normalization preserve a fixed internal commutant. -/
theorem density_commute (K J : Mat) (hKJ : Commute K J) :
    Commute (density K) J :=
  hKJ.exp_left.smul_left (partition K)⁻¹

end InfoGeometry.Thermo.RealMatrixGibbsOrbit

namespace InfoGeometry.Thermo.RealDensityRadialFlow

open SouriauHilbertSchmidtOnsager

variable {n : ℕ}

/-- Radial mixing preserves the commutant of any chosen internal real operator. -/
theorem radialMix_commute (r : ℝ) (ρ J : MatrixSpace n)
    (hρJ : Commute ρ J) : Commute (radialMix r ρ) J :=
  (hρJ.smul_left r).add_left ((uniformDensity_commute J).smul_left (1 - r))

/-- Trace normalization preserves the same internal commutant. -/
theorem traceNormalize_commute (A J : MatrixSpace n) (hAJ : Commute A J) :
    Commute (traceNormalize A) J :=
  hAJ.smul_left (Matrix.trace A)⁻¹

end InfoGeometry.Thermo.RealDensityRadialFlow
