import InfoGeometry.Topological.FibonacciAnyons
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Topological.FibonacciCasimir

Finite algebraic Casimir readbacks for the Fibonacci braid surface.

The Casimirs here are the closed finite invariants of the middle braid
conjugation `B = F R F`: trace, determinant, and discriminant.  No colimit
existence theorem is asserted here.
-/

set_option autoImplicit false

namespace InfoGeometry.Topological.FibonacciAnyons

open Matrix

variable {K : Type*} [CommRing K]

/-- Trace of a `2 × 2` matrix. -/
def trace2 (M : Matrix (Fin 2) (Fin 2) K) : K :=
  M 0 0 + M 1 1

/-- Determinant of a `2 × 2` matrix, used as the second finite Casimir. -/
def det2 (M : Matrix (Fin 2) (Fin 2) K) : K :=
  M.det

/-- Characteristic discriminant `tr² - 4 det` for a `2 × 2` matrix. -/
def discriminant2 (M : Matrix (Fin 2) (Fin 2) K) : K :=
  trace2 M ^ 2 - (4 : K) * det2 M

/-- The finite `R` trace Casimir is the sum of its two diagonal phases. -/
theorem trace2_R_matrixOf (q qInv : K) :
    trace2 (R_matrixOf q qInv) = qInv ^ 4 + q ^ 3 := by
  simp [trace2, R_matrixOf]

/-- The Fibonacci fusion matrix has vanishing trace. -/
theorem trace2_F_matrixOf (τ sqrtτ : K) :
    trace2 (F_matrixOf τ sqrtτ) = 0 := by
  simp [trace2, F_matrixOf]

/-- Trace is cyclic for `2 × 2` matrices. -/
theorem trace2_mul_comm
    (A B : Matrix (Fin 2) (Fin 2) K) :
    trace2 (A * B) = trace2 (B * A) := by
  simp [trace2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/--
Trace Casimir invariance for the Fibonacci middle braid block.

If `F² = 1`, then `B = F R F` has the same trace as `R`.
-/
theorem trace2_B_eq_trace2_R_of_F_involution
    (q qInv τ sqrtτ : K)
    (hF : F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ =
      (1 : Matrix (Fin 2) (Fin 2) K)) :
    trace2 (B_matrixOf q qInv τ sqrtτ) =
      trace2 (R_matrixOf q qInv) := by
  calc
    trace2 (B_matrixOf q qInv τ sqrtτ) =
        trace2 ((F_matrixOf τ sqrtτ * R_matrixOf q qInv) *
          F_matrixOf τ sqrtτ) := by
          rfl
    _ = trace2 (F_matrixOf τ sqrtτ *
        (F_matrixOf τ sqrtτ * R_matrixOf q qInv)) := by
          rw [trace2_mul_comm]
    _ = trace2 ((F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ) *
        R_matrixOf q qInv) := by
          rw [mul_assoc]
    _ = trace2 ((1 : Matrix (Fin 2) (Fin 2) K) *
        R_matrixOf q qInv) := by
          rw [hF]
    _ = trace2 (R_matrixOf q qInv) := by
          simp

/--
Determinant Casimir invariance for the Fibonacci middle braid block.

If `F² = 1`, then `det F * det F = 1`, so `det(F R F) = det R`.
-/
theorem det2_B_eq_det2_R_of_F_involution
    (q qInv τ sqrtτ : K)
    (hF : F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ =
      (1 : Matrix (Fin 2) (Fin 2) K)) :
    det2 (B_matrixOf q qInv τ sqrtτ) =
      det2 (R_matrixOf q qInv) := by
  have hFdet : det2 (F_matrixOf τ sqrtτ) * det2 (F_matrixOf τ sqrtτ) = 1 := by
    have h := congrArg Matrix.det hF
    simpa [det2, Matrix.det_mul] using h
  calc
    det2 (B_matrixOf q qInv τ sqrtτ) =
        det2 (F_matrixOf τ sqrtτ * R_matrixOf q qInv *
          F_matrixOf τ sqrtτ) := by
          rfl
    _ = (det2 (F_matrixOf τ sqrtτ) * det2 (R_matrixOf q qInv)) *
        det2 (F_matrixOf τ sqrtτ) := by
          simp [det2, Matrix.det_mul]
    _ = (det2 (F_matrixOf τ sqrtτ) * det2 (F_matrixOf τ sqrtτ)) *
        det2 (R_matrixOf q qInv) := by
          ring
    _ = det2 (R_matrixOf q qInv) := by
          rw [hFdet]
          simp

/--
Discriminant Casimir invariance for the Fibonacci middle braid block.
-/
theorem discriminant2_B_eq_discriminant2_R_of_F_involution
    (q qInv τ sqrtτ : K)
    (hF : F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ =
      (1 : Matrix (Fin 2) (Fin 2) K)) :
    discriminant2 (B_matrixOf q qInv τ sqrtτ) =
      discriminant2 (R_matrixOf q qInv) := by
  simp [
    discriminant2,
    trace2_B_eq_trace2_R_of_F_involution q qInv τ sqrtτ hF,
    det2_B_eq_det2_R_of_F_involution q qInv τ sqrtτ hF,
  ]

end InfoGeometry.Topological.FibonacciAnyons
