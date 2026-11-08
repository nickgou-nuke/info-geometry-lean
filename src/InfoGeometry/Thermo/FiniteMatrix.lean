import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Finite-Dimensional Determinant-Volume Model

Concrete finite-dimensional determinant-relative-volume layer over finite real
matrices.

This is not the statistical Gibbs/Massieu partition function
`Tr(exp (-βH))`.  The determinant readout here is an H¹ volume/Jacobian
quantity.  The finite statistical partition and Fisher covariance layer is
owned by `InfoGeometry.Algebraic.CartanExponentialFamily` and
`InfoGeometry.Thermodynamics.FiniteGibbsRelative`.
-/

namespace InfoGeometry.Thermo

open Matrix

section FiniteMatrixThermal

variable {n : ℕ}

/-- Finite operator algebra on `ℝ^n` (matrix model). -/
abbrev Op (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite-dimensional determinant-volume model with Hamiltonian `H` and inverse temperature `β`. -/
structure ThermalModel (n : ℕ) where
  H : Op n
  β : ℝ

namespace ThermalModel

/-- Unnormalized log-density (the Gibbs exponent). -/
noncomputable def logUnnormalizedDensity (M : ThermalModel n) : Op n :=
  (-M.β) • M.H

/-- Gibbs weight `e^{-βH}`. -/
noncomputable def gibbsWeight (M : ThermalModel n) : Op n :=
  NormedSpace.exp (M.logUnnormalizedDensity)

/-- Determinant-volume cocycle readout, not the trace-exponential partition. -/
noncomputable def volumeCocycle (M : ThermalModel n) : ℝ :=
  Matrix.det (M.gibbsWeight)

/-- The determinant-volume cocycle is nonzero because matrix exponentials are units. -/
lemma volumeCocycle_ne_zero (M : ThermalModel n) :
    M.volumeCocycle ≠ 0 := by
  have hUnitMat : IsUnit (NormedSpace.exp M.logUnnormalizedDensity) :=
    Matrix.isUnit_exp M.logUnnormalizedDensity
  have hUnitDet : IsUnit (Matrix.det (NormedSpace.exp M.logUnnormalizedDensity)) :=
    (Matrix.isUnit_iff_isUnit_det (A := NormedSpace.exp M.logUnnormalizedDensity)).mp hUnitMat
  simpa [volumeCocycle, gibbsWeight] using (isUnit_iff_ne_zero.mp hUnitDet)

/--
Backward-compatible alias for `volumeCocycle`.

Prefer `volumeCocycle` in new code.  This is not the statistical Gibbs/Massieu
partition function `Tr(exp (-βH))`.
-/
noncomputable abbrev partitionFunction (M : ThermalModel n) : ℝ :=
  M.volumeCocycle

/-- Backward-compatible nonzero lemma for the determinant-volume alias. -/
lemma partitionFunction_ne_zero (M : ThermalModel n) :
    M.partitionFunction ≠ 0 :=
  M.volumeCocycle_ne_zero

/-- Matrix scaled by determinant-volume readout, not a trace-normalized density matrix. -/
noncomputable def volumeNormalizedMatrix (M : ThermalModel n) : Op n :=
  (M.volumeCocycle)⁻¹ • M.gibbsWeight

/--
Backward-compatible alias for `volumeNormalizedMatrix`.

Prefer `volumeNormalizedMatrix` in new code.  This is not a trace-normalized
statistical density matrix.
-/
noncomputable abbrev densityMatrix (M : ThermalModel n) : Op n :=
  M.volumeNormalizedMatrix

/-- Determinant/log-volume readout functional. -/
noncomputable def logVolumeExpectation (M : ThermalModel n) (A : Op n) : ℝ :=
  Real.log (|Matrix.det (M.volumeNormalizedMatrix * A)|)

/--
Backward-compatible alias for `logVolumeExpectation`.

Prefer `logVolumeExpectation` in new code.  This is a log-volume readout, not a
statistical Gibbs expectation.
-/
noncomputable abbrev gibbsExpectation (M : ThermalModel n) (A : Op n) : ℝ :=
  M.logVolumeExpectation A

/-- Heisenberg/modular conjugation by `H` at time `t`: `A ↦ e^{tH} A e^{-tH}`. -/
noncomputable def modularShift (M : ThermalModel n) (t : ℝ) (A : Op n) : Op n :=
  (NormedSpace.exp (t • M.H)) * A * (NormedSpace.exp ((-t) • M.H))

/-- Modular conjugation driven by the unnormalized log-density generator. -/
noncomputable def modularShiftFromLogDensity (M : ThermalModel n) (t : ℝ) (A : Op n) : Op n :=
  (NormedSpace.exp (t • M.logUnnormalizedDensity)) * A *
    (NormedSpace.exp ((-t) • M.logUnnormalizedDensity))

/-- Relation between log-density flow and Hamiltonian flow. -/
lemma modularShiftFromLogDensity_eq_modularShift
    (M : ThermalModel n) (t : ℝ) (A : Op n) :
    M.modularShiftFromLogDensity t A = M.modularShift ((-M.β) * t) A := by
  unfold modularShiftFromLogDensity modularShift logUnnormalizedDensity
  simp [smul_smul, mul_assoc, mul_comm]

/-- A KMS-like relation for a state `ω` at inverse temperature `β`. -/
def SatisfiesKMSLike (M : ThermalModel n) (ω : Op n → ℝ) : Prop :=
  ∀ A B : Op n, ω (A * M.modularShift M.β B) = ω (B * A)

/-- KMS-like relation restricted to a chosen observable subset. -/
def SatisfiesKMSLikeOn (M : ThermalModel n) (ω : Op n → ℝ) (Obs : Set (Op n)) : Prop :=
  ∀ {A B}, A ∈ Obs → B ∈ Obs → ω (A * M.modularShift M.β B) = ω (B * A)

@[simp] lemma modularShift_zero (M : ThermalModel n) (A : Op n) :
    M.modularShift 0 A = A := by
  unfold modularShift
  simp

end ThermalModel

end FiniteMatrixThermal

end InfoGeometry.Thermo
