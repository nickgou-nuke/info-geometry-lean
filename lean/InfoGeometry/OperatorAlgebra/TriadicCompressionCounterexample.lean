/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentCompression
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A four-dimensional limit on strict compression claims

The full real matrix algebra contains three orthogonal projections and a
self-adjoint idempotent of trace one with two nonzero outgoing channels.
Its compression has a nonzero, positive semidefinite defect, but that defect
annihilates a nonzero vector inside the compressed corner. The compression
also has trace `1 / 3`, and normalizing it yields an idempotent.

Thus nonzero channels do not imply positive definiteness on the corner,
faithfulness of the compression, or a mixed normalized state. The matrices
are finite counterexamples to these implications, not substitutes for the
general noncommutative compression theorems.
-/

namespace InfoGeometry.OperatorAlgebra.TriadicCompressionCounterexample

open Matrix

noncomputable section

/-- The observed corner has two real dimensions. -/
def p : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The first complementary channel. -/
def q : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]

/-- The second complementary channel. -/
def r : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1]

/-- The complete triple is realized by the actual normalized tripotent API. -/
def polarization : Matrix (Fin 4) (Fin 4) ℝ := p - r

/-- The orthogonal projection onto the span of `(1, 0, 1, 1)`. -/
def x : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/3, 0, 1/3, 1/3; 0, 0, 0, 0;
     1/3, 0, 1/3, 1/3; 1/3, 0, 1/3, 1/3]

def rho : Matrix (Fin 4) (Fin 4) ℝ := p * x * p

/-- This uses the sign `rho - rho²`, opposite to `IdempotencyDefect.defect`. -/
def compressionDefect : Matrix (Fin 4) (Fin 4) ℝ := rho - rho * rho

/-- A nonzero vector in the observed corner, independent of its occupied line. -/
def kernelVector : Fin 4 → ℝ := ![0, 1, 0, 0]

theorem p_idempotent : p * p = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, mul_apply, Fin.sum_univ_succ]

theorem q_idempotent : q * q = q := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [q, mul_apply, Fin.sum_univ_succ]

theorem r_idempotent : r * r = r := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [r, mul_apply, Fin.sum_univ_succ]

theorem p_selfadjoint : pᴴ = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, conjTranspose_apply]

theorem q_selfadjoint : qᴴ = q := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [q, conjTranspose_apply]

theorem r_selfadjoint : rᴴ = r := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [r, conjTranspose_apply]

theorem projection_sum : p + q + r = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, q, r]

theorem projections_pairwise_orthogonal :
    p * q = 0 ∧ q * p = 0 ∧ p * r = 0 ∧ r * p = 0 ∧
      q * r = 0 ∧ r * q = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [p, q, r, mul_apply, Fin.sum_univ_succ]

theorem polarization_tripotent : polarization * polarization * polarization = polarization := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polarization, p, r, mul_apply, Fin.sum_univ_succ]

theorem polarization_selfadjoint : star polarization = polarization := by
  simp only [polarization, star_sub, Matrix.star_eq_conjTranspose, p_selfadjoint,
    r_selfadjoint]

theorem normalized_projPos : InfoGeometry.Physics.Algebra.projPos polarization = p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.Algebra.projPos, polarization, p, r,
      mul_apply, Fin.sum_univ_succ]

theorem normalized_projZero : InfoGeometry.Physics.Algebra.projZero polarization = q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.Algebra.projZero, polarization, p, q, r,
      mul_apply, Fin.sum_univ_succ]

theorem normalized_projNeg : InfoGeometry.Physics.Algebra.projNeg polarization = r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Physics.Algebra.projNeg, polarization, p, r,
      mul_apply, Fin.sum_univ_succ]

theorem x_idempotent : x * x = x := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [x, mul_apply, Fin.sum_univ_succ]

theorem x_selfadjoint : xᴴ = x := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [x, conjTranspose_apply]

theorem x_posSemidef : x.PosSemidef := by
  simpa only [x_selfadjoint, x_idempotent] using posSemidef_self_mul_conjTranspose x

theorem x_trace : trace x = 1 := by
  norm_num [trace, diag, x, Fin.sum_univ_succ]

/-- The projection and state genuinely fail to commute in the full matrix algebra. -/
theorem p_x_noncommute : p * x ≠ x * p := by
  intro h
  have h02 := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m 0 2) h
  norm_num [p, x, mul_apply, Fin.sum_univ_succ] at h02

theorem first_channel_ne_zero : p * x * q ≠ 0 := by
  intro h
  have h02 := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m 0 2) h
  norm_num [p, q, x, mul_apply, Fin.sum_univ_succ] at h02

theorem second_channel_ne_zero : p * x * r ≠ 0 := by
  intro h
  have h03 := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m 0 3) h
  norm_num [p, r, x, mul_apply, Fin.sum_univ_succ] at h03

theorem rho_eq : rho =
    !![1/3, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rho, p, x, mul_apply, Fin.sum_univ_succ]

theorem rho_posSemidef : rho.PosSemidef := by
  simpa only [p_selfadjoint, rho] using x_posSemidef.conjTranspose_mul_mul_same p

/-- The existing general compression theorem computes this example's return product. -/
theorem compressionDefect_eq_return_product :
    compressionDefect = p * x * (1 - p) * x * p := by
  have h := InfoGeometry.Core.PeirceCompressionDefect.compression_mul_defect
    p x x p_idempotent
  simpa only [x_idempotent, rho, compressionDefect] using h

theorem compressionDefect_eq : compressionDefect =
    !![2/9, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  rw [compressionDefect, rho_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mul_apply, Fin.sum_univ_succ]

theorem compressionDefect_ne_zero : compressionDefect ≠ 0 := by
  intro h
  have h00 := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m 0 0) h
  norm_num [compressionDefect_eq] at h00

theorem compressionDefect_eq_two_thirds_rho :
    compressionDefect = (2 / 3 : ℝ) • rho := by
  rw [compressionDefect_eq, rho_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem compressionDefect_posSemidef : compressionDefect.PosSemidef := by
  rw [compressionDefect_eq_two_thirds_rho]
  exact rho_posSemidef.smul (by norm_num : (0 : ℝ) ≤ 2 / 3)

theorem rho_not_idempotent : rho * rho ≠ rho := by
  intro h
  apply compressionDefect_ne_zero
  simp only [compressionDefect, h, sub_self]

theorem kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Fin 4 → ℝ => v 1) h
  norm_num [kernelVector] at h1

theorem p_mulVec_kernelVector : p *ᵥ kernelVector = kernelVector := by
  ext i
  fin_cases i <;> norm_num [p, kernelVector, mulVec, dotProduct, Fin.sum_univ_succ]

theorem rho_mulVec_kernelVector : rho *ᵥ kernelVector = 0 := by
  rw [rho_eq]
  ext i
  fin_cases i <;> norm_num [kernelVector, mulVec, dotProduct, Fin.sum_univ_succ]

theorem compressionDefect_mulVec_kernelVector :
    compressionDefect *ᵥ kernelVector = 0 := by
  rw [compressionDefect_eq]
  ext i
  fin_cases i <;> norm_num [kernelVector, mulVec, dotProduct, Fin.sum_univ_succ]

/-- The failure of strict positivity occurs inside the observed corner itself. -/
theorem compressionDefect_not_strict_on_corner :
    ¬ ∀ v : Fin 4 → ℝ, p *ᵥ v = v → v ≠ 0 →
      0 < star v ⬝ᵥ (compressionDefect *ᵥ v) := by
  intro h
  have hpos := h kernelVector p_mulVec_kernelVector kernelVector_ne_zero
  rw [compressionDefect_mulVec_kernelVector] at hpos
  simpa using hpos

theorem compressionDefect_not_posDef : ¬ compressionDefect.PosDef := by
  intro h
  have hpos := h.dotProduct_mulVec_pos kernelVector_ne_zero
  rw [compressionDefect_mulVec_kernelVector] at hpos
  simpa using hpos

theorem rho_trace : trace rho = (1 / 3 : ℝ) := by
  rw [rho_eq]
  norm_num [trace, diag, Fin.sum_univ_succ]

theorem rho_trace_ne_one : trace rho ≠ 1 := by
  rw [rho_trace]
  norm_num

/-- Trace normalization of this compressed pure projection is still a projection. -/
theorem normalized_rho_idempotent :
    ((3 : ℝ) • rho) * ((3 : ℝ) • rho) = (3 : ℝ) • rho := by
  rw [rho_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mul_apply, Fin.sum_univ_succ]

theorem normalized_rho_trace : trace ((3 : ℝ) • rho) = 1 := by
  rw [trace_smul, rho_trace]
  norm_num

end
end InfoGeometry.OperatorAlgebra.TriadicCompressionCounterexample
