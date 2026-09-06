import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Finite-Dimensional Thermal Model (Determinant Version)

Concrete finite-dimensional thermal/KMS layer over finite real matrices, with
partition/observables encoded by determinant-relative-volume quantities.
-/

namespace InfoGeometry.Thermo

open Matrix

section FiniteMatrixThermal

variable {n : ℕ}

/-- Finite operator algebra on `ℝ^n` (matrix model). -/
abbrev Op (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite-dimensional thermal model with Hamiltonian `H` and inverse temperature `β`. -/
structure ThermalModel (n : ℕ) where
  H : Op n
  β : ℝ
  partition_ne_zero : Matrix.det (NormedSpace.exp ((-β) • H)) ≠ 0

namespace ThermalModel

/-- Unnormalized log-density (the Gibbs exponent). -/
noncomputable def logUnnormalizedDensity (M : ThermalModel n) : Op n :=
  (-M.β) • M.H

/-- Gibbs weight `e^{-βH}`. -/
noncomputable def gibbsWeight (M : ThermalModel n) : Op n :=
  NormedSpace.exp (M.logUnnormalizedDensity)

/-- Partition function as determinant-relative volume. -/
noncomputable def partitionFunction (M : ThermalModel n) : ℝ :=
  Matrix.det (M.gibbsWeight)

lemma partitionFunction_ne_zero (M : ThermalModel n) :
    M.partitionFunction ≠ 0 := by
  simpa [partitionFunction, gibbsWeight, logUnnormalizedDensity] using M.partition_ne_zero

/-- Normalized Gibbs matrix by determinant partition scalar. -/
noncomputable def densityMatrix (M : ThermalModel n) : Op n :=
  (M.partitionFunction)⁻¹ • M.gibbsWeight

/-- Determinant/log-volume expectation functional. -/
noncomputable def gibbsExpectation (M : ThermalModel n) (A : Op n) : ℝ :=
  Real.log (|Matrix.det (M.densityMatrix * A)|)

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
