import InfoGeometry.Modular.NambuGradedSuperalgebraBridge
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Ordinary trace versus supertrace in a Krein quadratic expression

For the existing doubled grading `Gamma`, `str(A) = tr(Gamma A)`.
Consequently `str(Z^sharp Z) = tr(Z^dagger Gamma Z)`, while
`tr(Z^sharp Z) = tr(Gamma Z^dagger Gamma Z)`. These expressions already differ
at `Z = 1`. This finite matrix statement does not identify a Zorn product with
associative matrix multiplication.
-/

noncomputable section

namespace InfoGeometry.Modular.Graded

open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]
local notation "BM" => Matrix (ι ⊕ ι) (ι ⊕ ι) R

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
