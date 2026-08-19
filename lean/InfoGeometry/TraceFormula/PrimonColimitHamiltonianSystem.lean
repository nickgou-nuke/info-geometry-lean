import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.TraceFormula.ColimitTrace
import InfoGeometry.TraceFormula.ItakuraSaitoMongeAmpere
import InfoGeometry.TraceFormula.DeRhamHolonomyStokes
import InfoGeometry.TraceFormula.FiniteISColimitInverseLimitSearch

/-!
# Finite-to-colimit Primon Hamiltonian readouts

This file assembles the existing finite matrix tower, finite Itakura--Saito
channel, normalized colimit trace, and finite holonomy confinement theorem.  The backward
state lane is represented by its explicit compatible family of linear
readouts; no completed projective-limit object or uniqueness theorem is
introduced here.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.PrimonHamiltonianColimit

open Matrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.TraceFormula.ColimitTrace
open InfoGeometry.TraceFormula.ItakuraSaito
open InfoGeometry.TraceFormula.DeRhamHolonomy

/-! ## Finite stage -/

/-- The finite Itakura--Saito energy relative to the identity reference. -/
def stageEffectiveHamiltonian (n : ℕ) (P : MatrixStage n) : ℝ :=
  itakuraSaitoDivergence n P (1 : MatrixStage n)

/-- The finite inverse-congruence Hessian readout. -/
def stageFisherHessian (n : ℕ) (P X : MatrixStage n) : MatrixStage n :=
  P⁻¹ * X * P⁻¹

/-- The inverse-congruence Hessian is self-adjoint for the trace pairing. -/
theorem stageFisherHessian_selfAdjoint (n : ℕ) (P X Y : MatrixStage n) :
    rawTrace n (Y * stageFisherHessian n P X) =
      rawTrace n (stageFisherHessian n P Y * X) := by
  unfold rawTrace stageFisherHessian
  calc
    Matrix.trace (Y * (P⁻¹ * X * P⁻¹)) =
        Matrix.trace ((Y * P⁻¹ * X) * P⁻¹) := by
          simp only [mul_assoc]
    _ = Matrix.trace (P⁻¹ * (Y * P⁻¹ * X)) := by
          exact Matrix.trace_mul_comm (Y * P⁻¹ * X) P⁻¹
    _ = Matrix.trace ((P⁻¹ * Y * P⁻¹) * X) := by
          simp only [mul_assoc]

/-! The inverse-congruence Hessian is compatible with the native matrix bond.
    The only hypothesis is the same finite nonsingularity condition used by
    the determinant owner for transport of inverses. -/

theorem stageFisherHessian_bond_compatible
    (n : ℕ) (P X : MatrixStage n) (hP : IsUnit P.det) :
    stageFisherHessian (n + 1) (matrixBond n P) (matrixBond n X) =
      matrixBond n (stageFisherHessian n P X) := by
  unfold stageFisherHessian
  rw [matrixBond_inv n P hP]
  rw [← map_mul, ← map_mul]

theorem stageFisherHessian_normalizedTrace_selfAdjoint
    (n : ℕ) (P X Y : MatrixStage n) :
    normalizedTrace n (Y * stageFisherHessian n P X) =
      normalizedTrace n (stageFisherHessian n P Y * X) := by
  simpa [normalizedTrace] using
    congrArg (fun t : ℝ => t / (2 ^ n : ℝ))
      (stageFisherHessian_selfAdjoint n P X Y)

/-! The normalized trace pairing is preserved by the Hessian bond. -/

theorem stageFisherHessian_pairing_bond_compatible
    (n : ℕ) (P X Y : MatrixStage n) (hP : IsUnit P.det) :
    normalizedTrace (n + 1)
        (matrixBond n Y *
          stageFisherHessian (n + 1) (matrixBond n P) (matrixBond n X)) =
      normalizedTrace n (Y * stageFisherHessian n P X) := by
  rw [stageFisherHessian_bond_compatible n P X hP]
  rw [← map_mul]
  exact normalizedTrace_compatible n
    (Y * stageFisherHessian n P X)

theorem stageEffectiveHamiltonian_identity_minimum (n : ℕ) :
    stageEffectiveHamiltonian n (1 : MatrixStage n) = -Real.log 1 := by
  unfold stageEffectiveHamiltonian
  apply itakuraSaito_self
  simp

theorem stageEffectiveHamiltonian_bond_compatible
    (n : ℕ) (P : MatrixStage n) :
    stageEffectiveHamiltonian (n + 1) (matrixBond n P) =
      2 * stageEffectiveHamiltonian n P := by
  unfold stageEffectiveHamiltonian
  simpa only [map_one] using
    (itakuraSaito_bond_compatible n P (1 : MatrixStage n) (by simp))

theorem normalized_stageEffectiveHamiltonian_bond_compatible
    (n : ℕ) (P : MatrixStage n) :
    (1 / (2 ^ (n + 1) : ℝ)) *
        stageEffectiveHamiltonian (n + 1) (matrixBond n P) =
      (1 / (2 ^ n : ℝ)) * stageEffectiveHamiltonian n P := by
  rw [stageEffectiveHamiltonian_bond_compatible n P]
  have hpow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [hpow]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

theorem normalized_stageEffectiveHamiltonian_bondMap_compatible
    (m n : ℕ) (h : m ≤ n) (P : MatrixStage m) :
    (1 / (2 ^ n : ℝ)) *
        stageEffectiveHamiltonian n (bondMap matrixBond m n h P) =
      (1 / (2 ^ m : ℝ)) * stageEffectiveHamiltonian m P := by
  simpa only [stageEffectiveHamiltonian, map_one] using
    (normalized_itakuraSaito_bondMap_compatible m n h P
      (1 : MatrixStage m) (by simp))

/-! ## Forward colimit -/

/-- A finite Hamiltonian observable viewed in the algebraic colimit. -/
def colimitHamiltonianObservable (n : ℕ) (H : MatrixStage n) :
    PrimonUHFAlgebra :=
  toColimit n H

@[simp] theorem colimitHamiltonian_bond (n : ℕ) (H : MatrixStage n) :
    colimitHamiltonianObservable (n + 1) (matrixBond n H) =
      colimitHamiltonianObservable n H := by
  exact toColimit_bond n H

/-! ## Compatible backward state readouts -/

/-- The normalized state at each finite stage. -/
abbrev projectiveTracialSequence (n : ℕ) : MatrixStage n →ₗ[ℝ] ℝ :=
  normalizedTraceLin n

theorem projective_trace_step (n : ℕ) (M : MatrixStage n) :
    projectiveTracialSequence (n + 1) (matrixBond n M) =
      projectiveTracialSequence n M := by
  change normalizedTrace (n + 1) (matrixBond n M) = normalizedTrace n M
  exact normalizedTrace_compatible n M

theorem projective_trace_iterated
    (m n : ℕ) (h : m ≤ n) (M : MatrixStage m) :
    projectiveTracialSequence n
        (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap
          matrixBond m n h M) =
      projectiveTracialSequence m M := by
  exact normalizedTraceLin_compatible m n h M

theorem colimit_vacuum_energy_evaluation (n : ℕ) (M : MatrixStage n) :
      InfoGeometry.TraceFormula.ColimitTrace.colimitTrace
        (colimitHamiltonianObservable n M) =
      projectiveTracialSequence n M := by
  change InfoGeometry.TraceFormula.ColimitTrace.colimitTrace (toColimit n M) =
    normalizedTrace n M
  exact InfoGeometry.TraceFormula.ColimitTrace.colimitTrace_evaluate_ringhom n M

/-! ## Native inverse-limit carrier -/

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology

variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]

/-- The compact-Hausdorff inverse-limit carrier already owned by the topology
    subsystem.  This is a carrier comparison, not a new projective trace. -/
abbrev inverseLimitCarrier : CompHaus :=
  symbolicBoundaryPrefixLimitCompHaus (A := A)

def inverseLimitCarrierIso :
    symbolicBoundaryCompHaus (A := A) ≅ inverseLimitCarrier (A := A) :=
  symbolicBoundaryPrefixLimitCompHausIso (A := A)

theorem inverseLimitCarrierIso_hom_inv_id :
    (inverseLimitCarrierIso (A := A)).hom ≫
        (inverseLimitCarrierIso (A := A)).inv = 𝟙 _ :=
  (inverseLimitCarrierIso (A := A)).hom_inv_id

theorem inverseLimitCarrierIso_inv_hom_id :
    (inverseLimitCarrierIso (A := A)).inv ≫
        (inverseLimitCarrierIso (A := A)).hom = 𝟙 _ :=
  (inverseLimitCarrierIso (A := A)).inv_hom_id

/-! ## Finite holonomy confinement readout -/

theorem colimit_holonomy_confinement (σ t : ℝ)
    (h_unitary :
      (translatedMonodromyGenerator σ t).transpose =
        -(translatedMonodromyGenerator σ t)) :
    σ = 1 / 2 :=
  stokes_holonomy_forces_critical_line σ t h_unitary

end InfoGeometry.TraceFormula.PrimonHamiltonianColimit
