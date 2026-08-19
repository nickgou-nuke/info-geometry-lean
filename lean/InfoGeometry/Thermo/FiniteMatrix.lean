import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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

/-- Finite-dimensional determinant-volume model with Hamiltonian `H` and inverse
temperature `β`, represented natively as a product. -/
abbrev ThermalModel (n : ℕ) := Op n × ℝ

namespace ThermalModel

@[simp] def H (M : ThermalModel n) : Op n := M.1
@[simp] def β (M : ThermalModel n) : ℝ := M.2

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

/-- Additive-time law for finite matrix modular conjugation. -/
lemma modularShift_add (M : ThermalModel n) (s t : ℝ) (A : Op n) :
    M.modularShift (s + t) A =
      M.modularShift s (M.modularShift t A) := by
  have h_comm : Commute (s • M.H) (t • M.H) :=
    ((Commute.refl M.H).smul_left s).smul_right t
  have h_comm_neg : Commute ((-t) • M.H) ((-s) • M.H) :=
    ((Commute.refl M.H).smul_left (-t)).smul_right (-s)
  unfold modularShift
  change
    NormedSpace.exp ((s + t) • M.H) * A *
        NormedSpace.exp ((-(s + t)) • M.H) =
      NormedSpace.exp (s • M.H) *
          (NormedSpace.exp (t • M.H) * A *
            NormedSpace.exp ((-t) • M.H)) *
        NormedSpace.exp ((-s) • M.H)
  calc
    NormedSpace.exp ((s + t) • M.H) * A *
          NormedSpace.exp ((-(s + t)) • M.H) =
        (NormedSpace.exp (s • M.H) * NormedSpace.exp (t • M.H)) * A *
          (NormedSpace.exp ((-t) • M.H) * NormedSpace.exp ((-s) • M.H)) := by
            rw [← Matrix.exp_add_of_commute _ _ h_comm]
            rw [← Matrix.exp_add_of_commute _ _ h_comm_neg]
            simp [add_smul, mul_assoc, add_comm]
    _ = NormedSpace.exp (s • M.H) *
          (NormedSpace.exp (t • M.H) * A *
            NormedSpace.exp ((-t) • M.H)) *
          NormedSpace.exp ((-s) • M.H) := by
            ring_nf
            simp [mul_assoc]

/-- Modular conjugation preserves multiplication of finite observables. -/
lemma modularShift_mul (M : ThermalModel n) (t : ℝ) (A B : Op n) :
    M.modularShift t (A * B) =
      M.modularShift t A * M.modularShift t B := by
  unfold modularShift
  have h_inv :
      NormedSpace.exp ((-t) • M.H) * NormedSpace.exp (t • M.H) =
        (1 : Op n) := by
    rw [← Matrix.exp_add_of_commute _ _]
    · simp
    · exact ((Commute.refl M.H).smul_left (-t)).smul_right t
  calc
    NormedSpace.exp (t • M.H) * (A * B) *
          NormedSpace.exp ((-t) • M.H) =
        NormedSpace.exp (t • M.H) * A *
          (NormedSpace.exp ((-t) • M.H) * NormedSpace.exp (t • M.H)) * B *
          NormedSpace.exp ((-t) • M.H) := by
            rw [h_inv]
            simp [mul_assoc]
    _ = (NormedSpace.exp (t • M.H) * A *
          NormedSpace.exp ((-t) • M.H)) *
          (NormedSpace.exp (t • M.H) * B *
            NormedSpace.exp ((-t) • M.H)) := by
            simp [mul_assoc]

end ThermalModel

end FiniteMatrixThermal

end InfoGeometry.Thermo
