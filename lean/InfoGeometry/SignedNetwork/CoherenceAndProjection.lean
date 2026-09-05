import Mathlib

/-!
# Coherent transport, measured transport, and conditional projection

A unitary frame change does not purify the maximally mixed state. Projection
and renormalization are separate operations, and the selected branch has an
explicit probability. A rational SU(2) rotation gives an exact regression
counterexample: coherent return is the identity, whereas sampling a basis
label after each edge is not coherent return.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.CoherenceAndProjection

open scoped Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Matrix conjugation on density or observable payloads. -/
def conjugate (U P : Mat2) : Mat2 := U * P * Uᴴ

/-- Unitary conjugation preserves an idempotent projector. -/
theorem conjugate_idempotent (U P : Mat2)
    (hU : Uᴴ * U = 1) (hP : P * P = P) :
    conjugate U P * conjugate U P = conjugate U P := by
  unfold conjugate
  calc
    (U * P * Uᴴ) * (U * P * Uᴴ) =
        U * P * (Uᴴ * U) * P * Uᴴ := by simp only [mul_assoc]
    _ = U * (P * P) * Uᴴ := by rw [hU]; simp only [mul_one, mul_assoc]
    _ = U * P * Uᴴ := by rw [hP]

/-- The Hermitian condition survives conjugation, without a unitarity hypothesis. -/
theorem conjugate_self_adjoint (U P : Mat2) (hP : Pᴴ = P) :
    (conjugate U P)ᴴ = conjugate U P := by
  simp [conjugate, Matrix.conjTranspose_mul, hP, mul_assoc]

/-- The maximally mixed qubit state. -/
def mixed : Mat2 := (1 / 2 : ℂ) • (1 : Mat2)

/-- Frame rotation alone cannot select a sense from the maximally mixed state. -/
theorem conjugate_mixed (U : Mat2) (hU : U * Uᴴ = 1) :
    conjugate U mixed = mixed := by
  simp only [conjugate, mixed, mul_smul_comm, mul_one, smul_mul_assoc, hU]

/-- The equal coherent superposition is not the maximally mixed density. -/
def balancedPure : Mat2 := !![1/2, 1/2; 1/2, 1/2]

theorem balancedPure_idempotent : balancedPure * balancedPure = balancedPure := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedPure, Matrix.mul_apply, Fin.sum_univ_two]

theorem balancedPure_ne_mixed : balancedPure ≠ mixed := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [balancedPure, mixed] at h01

/-- The unnormalized branch after filtering the mixed state by an idempotent. -/
theorem selected_mixed_branch (P : Mat2) (hP : P * P = P) :
    P * mixed * P = (1 / 2 : ℂ) • P := by
  simp only [mixed, mul_smul_comm, mul_one, smul_mul_assoc, hP]

/-- For a trace-one projector the branch probability is exactly one half. -/
theorem selected_mixed_probability (P : Mat2) (hP : P * P = P)
    (htr : Matrix.trace P = 1) : Matrix.trace (P * mixed * P) = 1 / 2 := by
  rw [selected_mixed_branch P hP, Matrix.trace_smul, htr]
  simp

/-- Normalized conditional branch. This is postselection, not unitary evolution. -/
theorem selected_mixed_normalized (P : Mat2) (hP : P * P = P)
    (htr : Matrix.trace P = 1) :
    (Matrix.trace (P * mixed * P))⁻¹ • (P * mixed * P) = P := by
  rw [selected_mixed_probability P hP htr, selected_mixed_branch P hP, smul_smul]
  norm_num

/-- A real rotation, regarded as a complex SU(2) matrix. -/
def rotation : Mat2 := !![3/5, -4/5; 4/5, 3/5]

theorem rotation_unitary : rotationᴴ * rotation = 1 ∧ rotation * rotationᴴ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem rotation_det : Matrix.det rotation = 1 := by
  norm_num [rotation, Matrix.det_fin_two]

/-- Population transition probabilities from a chosen-basis measurement. -/
def bornMatrix (U : Mat2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => Complex.normSq (U i j)

/-- Coherent transport out and back returns every amplitude. -/
theorem coherent_return : rotationᴴ * rotation = 1 := rotation_unitary.1

/-- Sampling a magnetic basis label on both legs loses the coherent return. -/
theorem measured_return_entry :
    (bornMatrix rotationᴴ * bornMatrix rotation) 0 0 = (337 / 625 : ℝ) := by
  norm_num [bornMatrix, rotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Complex.normSq_apply]

/-- An exact obstruction to replacing Wigner amplitudes by per-edge Born sampling. -/
theorem bornMatrix_not_multiplicative :
    bornMatrix (rotationᴴ * rotation) ≠ bornMatrix rotationᴴ * bornMatrix rotation := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  rw [coherent_return, measured_return_entry] at h00
  norm_num [bornMatrix, Complex.normSq_apply] at h00

end InfoGeometry.SignedNetwork.CoherenceAndProjection
