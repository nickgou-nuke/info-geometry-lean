import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix
open scoped BigOperators

namespace InfoGeometry.QuantumGeometry.SLD

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- Anti-commutator (Jordan product) of two matrices: {A, B} = A * B + B * A -/
def jordanProd (A B : Mat) : Mat :=
  A * B + B * A

/-- Symmetric Logarithmic Derivative (SLD) condition:
    An operator L is the SLD of a density variation dRho with respect to rho if
    dRho = (1/2) * (rho * L + L * rho) -/
def IsSLD (rho dRho L : Mat) : Prop :=
  dRho = (1 / 2 : ℂ) • jordanProd rho L

/-- Quantum Fisher Information (SLD metric) between two SLD operators:
    g(L₁, L₂) = (1/2) * Tr(rho * {L₁, L₂}) -/
def sldFisherInner (rho L₁ L₂ : Mat) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (rho * jordanProd L₁ L₂)

/-- Linearity in the first argument -/
theorem sldFisherInner_add_left (rho L₁ L₁' L₂ : Mat) :
    sldFisherInner rho (L₁ + L₁') L₂ = sldFisherInner rho L₁ L₂ + sldFisherInner rho L₁' L₂ := by
  dsimp [sldFisherInner, jordanProd]
  have h : (L₁ + L₁') * L₂ + L₂ * (L₁ + L₁') = (L₁ * L₂ + L₂ * L₁) + (L₁' * L₂ + L₂ * L₁') := by
    noncomm_ring
  rw [h, mul_add, Matrix.trace_add, mul_add]

/-- Linearity in the second argument -/
theorem sldFisherInner_add_right (rho L₁ L₂ L₂' : Mat) :
    sldFisherInner rho L₁ (L₂ + L₂') = sldFisherInner rho L₁ L₂ + sldFisherInner rho L₁ L₂' := by
  dsimp [sldFisherInner, jordanProd]
  have h : L₁ * (L₂ + L₂') + (L₂ + L₂') * L₁ = (L₁ * L₂ + L₂ * L₁) + (L₁ * L₂' + L₂' * L₁) := by
    noncomm_ring
  rw [h, mul_add, Matrix.trace_add, mul_add]

/-- Scalar compatibility -/
theorem sldFisherInner_smul_left (c : ℂ) (rho L₁ L₂ : Mat) :
    sldFisherInner rho (c • L₁) L₂ = c * sldFisherInner rho L₁ L₂ := by
  dsimp [sldFisherInner, jordanProd]
  have h : (c • L₁) * L₂ + L₂ * (c • L₁) = c • (L₁ * L₂ + L₂ * L₁) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [h, mul_smul_comm, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- Scalar compatibility in the second SLD argument. -/
theorem sldFisherInner_smul_right (c : ℂ) (rho L₁ L₂ : Mat) :
    sldFisherInner rho L₁ (c • L₂) = c * sldFisherInner rho L₁ L₂ := by
  dsimp [sldFisherInner, jordanProd]
  have h : L₁ * (c • L₂) + (c • L₂) * L₁ =
      c • (L₁ * L₂ + L₂ * L₁) := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  rw [h, mul_smul_comm, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

@[simp]
theorem sldFisherInner_zero_left (rho L₂ : Mat) :
    sldFisherInner rho 0 L₂ = 0 := by
  simpa using sldFisherInner_smul_left (n := n) (c := (0 : ℂ)) rho (1 : Mat) L₂

@[simp]
theorem sldFisherInner_zero_right (rho L₁ : Mat) :
    sldFisherInner rho L₁ 0 = 0 := by
  simpa using sldFisherInner_smul_right (n := n) (c := (0 : ℂ)) rho L₁ (1 : Mat)

/-- Symmetry under cyclic trace property or commutativity -/
theorem sldFisherInner_comm (rho L₁ L₂ : Mat) :
    sldFisherInner rho L₁ L₂ = sldFisherInner rho L₂ L₁ := by
  dsimp [sldFisherInner, jordanProd]
  have h : L₁ * L₂ + L₂ * L₁ = L₂ * L₁ + L₁ * L₂ := by
    abel
  rw [h]

/-- Quadratic form of the SLD Fisher Information metric:
    g(L, L) = Tr(rho * L²) when rho and L commute -/
theorem sldFisherInner_self_commuting (rho L : Mat) :
    sldFisherInner rho L L = Matrix.trace (rho * (L * L)) := by
  dsimp [sldFisherInner, jordanProd]
  have h : L * L + L * L = (2 : ℂ) • (L * L) := by
    rw [two_smul]
  rw [h, mul_smul_comm, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- Positive semi-definiteness in the diagonal/classical basis:
    If rho = diag(p) with p_i ≥ 0 and L = diag(l), then
    Tr(rho * L²) = ∑_i p_i * l_i² ≥ 0 -/
theorem sldFisher_diagonal_pos_semidef (p l : n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ (Matrix.trace (Matrix.diagonal (fun i => (p i : ℂ)) *
          (Matrix.diagonal (fun i => (l i : ℂ)) * Matrix.diagonal (fun i => (l i : ℂ))))).re := by
  have h_mul : Matrix.diagonal (fun i => (p i : ℂ)) *
        (Matrix.diagonal (fun i => (l i : ℂ)) * Matrix.diagonal (fun i => (l i : ℂ))) =
      Matrix.diagonal (fun i => ((p i * l i ^ 2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    · simp only [diagonal_apply_ne _ hij, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h_mul, Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro i _
  have h_sq : 0 ≤ l i ^ 2 := sq_nonneg (l i)
  exact mul_nonneg (hp i) h_sq

end InfoGeometry.QuantumGeometry.SLD

end noncomputable section
