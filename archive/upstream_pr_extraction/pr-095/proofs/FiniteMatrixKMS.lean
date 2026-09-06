import Mathlib
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

open Matrix
open scoped ComplexConjugate
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace FiniteMatrixKMS

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev FiniteObservable (n : Type*) [Fintype n] := Matrix n n ℂ

structure DensityMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  val : Matrix n n ℂ
  hermitian : valᴴ = val
  pos : 0 ≤ val
  trace_one : trace val = 1

def matrixState (ρ : DensityMatrix n) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun A := trace (ρ.val * A)
  map_add' A B := by
    simp only [Matrix.mul_add, trace_add]
  map_smul' c A := by
    simp only [RingHom.id_apply, Matrix.mul_smul, trace_smul]

theorem matrixState_apply (ρ : DensityMatrix n) (A : Matrix n n ℂ) :
    matrixState ρ A = trace (ρ.val * A) := rfl

theorem matrixState_one (ρ : DensityMatrix n) :
    matrixState ρ 1 = 1 := by
  simp only [matrixState_apply, Matrix.mul_one, ρ.trace_one]

omit [DecidableEq n] in
theorem trace_mul_comm_lem (A B : Matrix n n ℂ) :
    trace (A * B) = trace (B * A) :=
  Matrix.trace_mul_comm A B

omit [DecidableEq n] in
theorem trace_mul_cycle_three (A B C : Matrix n n ℂ) :
    trace (A * B * C) = trace (B * C * A) := by
  simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm A (B * C)

theorem trace_conjugation (A U U_inv : Matrix n n ℂ) (hU_U_inv : U * U_inv = 1) :
    trace (U_inv * A * U) = trace A := by
  calc
    trace (U_inv * A * U) = trace (U * (U_inv * A)) := by rw [Matrix.trace_mul_comm]
    _ = trace ((U * U_inv) * A) := by rw [← Matrix.mul_assoc]
    _ = trace (1 * A) := by rw [hU_U_inv]
    _ = trace A := by rw [Matrix.one_mul]

theorem matrixState_star (ρ : DensityMatrix n) (A : Matrix n n ℂ) :
    matrixState ρ Aᴴ = star (matrixState ρ A) := by
  rw [matrixState_apply, matrixState_apply]
  have ht : star (trace (ρ.val * A)) = trace ((ρ.val * A)ᴴ) := by
    exact (Matrix.trace_conjTranspose (ρ.val * A)).symm
  rw [ht, Matrix.conjTranspose_mul, ρ.hermitian, Matrix.trace_mul_comm]

theorem matrixState_positive [Nonempty n] (ρ : DensityMatrix n) (A : Matrix n n ℂ) :
    0 ≤ (matrixState ρ (Aᴴ * A)).re := by
  exact InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.weightedTrace_nonneg
    ρ.val (Matrix.nonneg_iff_posSemidef.mp ρ.pos) A

/-- Finite-Dimensional Dynamics -/
structure FiniteStarDynamics (n : Type*) [Fintype n] [DecidableEq n] where
  α : ℝ → (Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ)
  map_zero : α 0 = 1
  map_add : ∀ s t, α (s + t) = α s * α t

def IsInvariantState (ω : Matrix n n ℂ →ₗ[ℂ] ℂ) (dyn : FiniteStarDynamics n) : Prop :=
  ∀ t A, ω (dyn.α t A) = ω A

/-- Finite Gibbs Specialization & KMS Identity -/

/- Finite weighted KMS identity.  The density and the imaginary-time
evolution are explicit inputs; no exponential or unproved existence claim is
introduced here. -/
theorem finite_weighted_kms
    (ρ : DensityMatrix n) (c : ℂ)
    (U U_inv : Matrix n n ℂ)
    (hρ : ρ.val = c • U)
    (hU_inv_U : U_inv * U = 1)
    (A B : Matrix n n ℂ) :
    matrixState ρ (A * (U * B * U_inv)) =
      matrixState ρ (B * A) := by
  rw [matrixState_apply, matrixState_apply, hρ]
  simp only [smul_mul_assoc, Matrix.trace_smul]
  congr 1
  calc
    Matrix.trace (U * (A * (U * B * U_inv))) =
        Matrix.trace (A * (U * B * U_inv) * U) := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm U (A * (U * B * U_inv))
    _ = Matrix.trace (A * U * B * (U_inv * U)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (A * U * B) := by
      rw [hU_inv_U]
      simp
    _ = Matrix.trace (U * (B * A)) := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm A (U * B)

end FiniteMatrixKMS
