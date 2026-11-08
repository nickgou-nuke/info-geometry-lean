/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.NambuGradedSuperalgebraBridge
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Ordinary trace versus supertrace in a Krein quadratic expression

For the existing doubled grading `Gamma`, `str(A) = tr(Gamma A)`.
Consequently `str(Z^sharp Z) = tr(Z^dagger Gamma Z)`, while
`tr(Z^sharp Z) = tr(Gamma Z^dagger Gamma Z)`. These expressions already differ
at `Z = 1`. This finite matrix statement does not identify a Zorn product with
associative matrix multiplication.

The constructive replacement is an exact conversion law: ordinary trace is
supertrace plus twice the trace of the negative diagonal block. For a Krein
square, that correction is twice the difference of the Gram traces of the
lower-right and upper-right blocks. Over the complex numbers their equality
is therefore equivalent to equality of these two Gram traces, with no
assumption that the whole operator is diagonal or self-adjoint.
-/

noncomputable section

namespace InfoGeometry.Modular.Graded

open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]
local notation "BM" => Matrix (ι ⊕ ι) (ι ⊕ ι) R

/-- Exact conversion between the ordinary and graded trace on the full carrier. -/
theorem trace_eq_superTrace_add_negative_block (A : BM) :
    Matrix.trace A = superTrace A + 2 * Matrix.trace (toBlocks₂₂ A) := by
  simp only [Matrix.trace, superTrace, Fintype.sum_sum_type,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.diag, Matrix.of_apply]
  ring

theorem superTrace_eq_trace_Gamma (A : BM) :
    superTrace A = Matrix.trace ((Gamma : BM) * A) := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Gamma, Matrix.fromBlocks_multiply, superTrace, Matrix.trace,
    Fintype.sum_sum_type, sub_eq_add_neg]

theorem superTrace_krein_square [StarRing R] (Z : BM) :
    superTrace ((Gamma : BM) * Zᴴ * Gamma * Z) =
      Matrix.trace (Zᴴ * Gamma * Z) := by
  rw [superTrace_eq_trace_Gamma]
  simp only [← mul_assoc, Gamma_sq, one_mul]

/-- The graded quadratic expression is the signed sum of four Gram traces. -/
theorem superTrace_krein_square_blocks [StarRing R] (A B C D : Matrix ι ι R) :
    superTrace ((Gamma : BM) * (fromBlocks A B C D)ᴴ * Gamma * fromBlocks A B C D) =
      Matrix.trace (Aᴴ * A) + Matrix.trace (Bᴴ * B) -
        Matrix.trace (Cᴴ * C) - Matrix.trace (Dᴴ * D) := by
  rw [superTrace_krein_square]
  simp [Gamma, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.trace, Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

/-- Exact correction term for the ordinary Krein quadratic trace. -/
theorem trace_krein_square_correction [StarRing R] (A B C D : Matrix ι ι R) :
    Matrix.trace ((Gamma : BM) * (fromBlocks A B C D)ᴴ * Gamma * fromBlocks A B C D) =
      superTrace ((Gamma : BM) * (fromBlocks A B C D)ᴴ * Gamma * fromBlocks A B C D) +
        2 * (Matrix.trace (Dᴴ * D) - Matrix.trace (Bᴴ * B)) := by
  rw [trace_eq_superTrace_add_negative_block]
  congr 1
  simp [Gamma, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.trace_neg]
  ring

/-- The two complex quadratic traces agree exactly when the negative-column
blocks have equal Gram traces. This replaces unconditional identification. -/
theorem trace_eq_superTrace_krein_square_iff (A B C D : Matrix ι ι ℂ) :
    Matrix.trace ((Gamma : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) *
        (fromBlocks A B C D)ᴴ * Gamma * fromBlocks A B C D) =
      superTrace ((Gamma : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) *
        (fromBlocks A B C D)ᴴ * Gamma * fromBlocks A B C D) ↔
      Matrix.trace (Dᴴ * D) = Matrix.trace (Bᴴ * B) := by
  rw [trace_krein_square_correction]
  constructor
  · intro h
    linear_combination (1 / 2 : ℂ) * h
  · intro h
    rw [h, sub_self, mul_zero, add_zero]

theorem krein_square_identity_trace [StarRing R] :
    Matrix.trace ((Gamma : BM) * (1 : BM)ᴴ * Gamma * (1 : BM)) =
      2 * (Fintype.card ι : R) := by
  simp [Gamma_sq, Fintype.card_sum, two_mul]

theorem krein_square_identity_superTrace [StarRing R] :
    superTrace ((Gamma : BM) * (1 : BM)ᴴ * Gamma * (1 : BM)) = 0 := by
  rw [superTrace_krein_square]
  simp

theorem trace_superTrace_counterexample :
    superTrace ((Gamma : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) *
      (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)ᴴ * Gamma * 1) ≠
    Matrix.trace ((Gamma : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) *
      (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)ᴴ * Gamma * 1) := by
  rw [krein_square_identity_superTrace, krein_square_identity_trace]
  norm_num

end InfoGeometry.Modular.Graded
