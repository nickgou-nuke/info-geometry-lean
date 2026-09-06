import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite-Dimensional Thermal Model (Matrix Version)

Concrete finite-dimensional thermal/KMS layer over finite real matrices.
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
  partition_ne_zero : Matrix.trace (NormedSpace.exp ((-β) • H)) ≠ 0

namespace ThermalModel

/-- Unnormalized log-density (the Gibbs exponent). -/
noncomputable def logUnnormalizedDensity (M : ThermalModel n) : Op n :=
  (-M.β) • M.H

/-- Gibbs weight `e^{-βH}`. -/
noncomputable def gibbsWeight (M : ThermalModel n) : Op n :=
  NormedSpace.exp (M.logUnnormalizedDensity)

/-- Partition function `Z = tr(e^{-βH})`. -/
noncomputable def partitionFunction (M : ThermalModel n) : ℝ :=
  Matrix.trace (M.gibbsWeight)

lemma partitionFunction_ne_zero (M : ThermalModel n) :
    M.partitionFunction ≠ 0 := by
  simpa [partitionFunction, gibbsWeight, logUnnormalizedDensity] using M.partition_ne_zero

/-- Normalized Gibbs density matrix `ρ = Z⁻¹ e^{-βH}`. -/
noncomputable def densityMatrix (M : ThermalModel n) : Op n :=
  (M.partitionFunction)⁻¹ • M.gibbsWeight

/-- Gibbs expectation functional `ω(A) = tr(ρ A)`. -/
noncomputable def gibbsExpectation (M : ThermalModel n) (A : Op n) : ℝ :=
  Matrix.trace (M.densityMatrix * A)

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

lemma densityMatrix_trace_one (M : ThermalModel n) :
    Matrix.trace (M.densityMatrix) = 1 := by
  unfold densityMatrix partitionFunction
  have hZ : Matrix.trace (M.gibbsWeight) ≠ 0 := M.partitionFunction_ne_zero
  calc
    Matrix.trace ((Matrix.trace (M.gibbsWeight))⁻¹ • M.gibbsWeight)
        = (Matrix.trace (M.gibbsWeight))⁻¹ * Matrix.trace (M.gibbsWeight) := by
            simp
    _ = 1 := by field_simp [hZ]

@[simp] lemma gibbsExpectation_one (M : ThermalModel n) :
    M.gibbsExpectation (1 : Op n) = 1 := by
  unfold gibbsExpectation
  simpa using M.densityMatrix_trace_one

lemma gibbsExpectation_add (M : ThermalModel n) (A B : Op n) :
    M.gibbsExpectation (A + B) = M.gibbsExpectation A + M.gibbsExpectation B := by
  unfold gibbsExpectation
  simp [Matrix.mul_add]

/-- Weighted trace cyclicity under a commuting density: if `ρ` commutes with `B`, then
`ω(AB) = ω(BA)` for the Gibbs state `ω(A)=tr(ρA)`. -/
lemma gibbsExpectation_mul_swap_of_commute_density
    (M : ThermalModel n)
    (A B : Op n)
    (hρB : Commute M.densityMatrix B) :
    M.gibbsExpectation (A * B) = M.gibbsExpectation (B * A) := by
  unfold gibbsExpectation
  calc
    Matrix.trace (M.densityMatrix * (A * B))
        = Matrix.trace ((M.densityMatrix * A) * B) := by
            simp [mul_assoc]
    _ = Matrix.trace (B * M.densityMatrix * A) := by
          simpa [mul_assoc] using Matrix.trace_mul_cycle M.densityMatrix A B
    _ = Matrix.trace ((M.densityMatrix * B) * A) := by
          rw [← hρB.eq]
    _ = Matrix.trace (M.densityMatrix * (B * A)) := by
          simp [mul_assoc]

/-- Cyclic Gibbs identity from modular fixed-point plus density commutation. -/
lemma gibbsExpectation_cyclic_of_modularFixed_commute
    (M : ThermalModel n)
    (A B : Op n)
    (hfixed : M.modularShift M.β B = B)
    (hρB : Commute M.densityMatrix B) :
    M.gibbsExpectation (A * M.modularShift M.β B) = M.gibbsExpectation (B * A) := by
  rw [hfixed]
  exact M.gibbsExpectation_mul_swap_of_commute_density A B hρB

/-- Packaged KMS-like property on fixed-point observables commuting with `ρ`. -/
theorem gibbsState_satisfiesKMSLike_on_fixed_commuting_set
    (M : ThermalModel n)
    (Obs : Set (Op n))
    (hfix : ∀ {B}, B ∈ Obs → M.modularShift M.β B = B)
    (hcomm : ∀ {B}, B ∈ Obs → Commute M.densityMatrix B) :
    SatisfiesKMSLikeOn (M := M) M.gibbsExpectation Obs := by
  intro A B hA hB
  exact M.gibbsExpectation_cyclic_of_modularFixed_commute A B (hfix hB) (hcomm hB)

@[deprecated gibbsExpectation_cyclic_of_modularFixed_commute (since := "2026-02-21")]
lemma gibbsExpectation_kms_like_of_fixedpoint
    (M : ThermalModel n)
    (A B : Op n)
    (hfixed : M.modularShift M.β B = B)
    (hρB : Commute M.densityMatrix B) :
    M.gibbsExpectation (A * M.modularShift M.β B) = M.gibbsExpectation (B * A) :=
  gibbsExpectation_cyclic_of_modularFixed_commute (M := M) A B hfixed hρB

@[deprecated gibbsState_satisfiesKMSLike_on_fixed_commuting_set (since := "2026-02-21")]
theorem gibbsState_satisfiesKMSLike_on
    (M : ThermalModel n)
    (Obs : Set (Op n))
    (hfix : ∀ {B}, B ∈ Obs → M.modularShift M.β B = B)
    (hcomm : ∀ {B}, B ∈ Obs → Commute M.densityMatrix B) :
    ∀ {A B}, A ∈ Obs → B ∈ Obs →
      M.gibbsExpectation (A * M.modularShift M.β B) = M.gibbsExpectation (B * A) :=
  gibbsState_satisfiesKMSLike_on_fixed_commuting_set (M := M) Obs hfix hcomm

end ThermalModel

end FiniteMatrixThermal

end InfoGeometry.Thermo
