import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Canonical.UHFCuntzGNSColimit

open Matrix
open CStarStateColimit.Native
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.UHFCuntzGNSColimit

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

/-!
# Concrete Matrix-Tower Normalized Trace Functionals

This module provides the finite complex matrix stages
`MatrixStage n := Matrix (Fin (2^n)) (Fin (2^n)) ℂ` and their normalized
linear trace functionals `A ↦ 2⁻ⁿ · Tr(A)`. It proves their finite algebraic
normalization, trace symmetry, star compatibility, and real-part positivity.
It does not construct a C*-completion, KMS state, or GNS Hilbert space.
-/

/-- Stage n of the matrix UHF tower is the 2ⁿ × 2ⁿ complex matrix algebra. -/
abbrev MatrixStage (n : ℕ) : Type := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-! The unnormalized trace is Mathlib's native matrix linear map.  The
normalization below is therefore a scalar multiple of a genuine linear map,
not a new evidence structure. -/

def matrixTraceFunctional (n : ℕ) : MatrixStage n →ₗ[ℂ] ℂ :=
  (1 / (2 ^ n : ℂ)) • Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ

/-- Normalized matrix trace functional at stage n: `2⁻ⁿ · Tr(A)`. -/
def matrixTraceState (n : ℕ) (A : MatrixStage n) : ℂ :=
  matrixTraceFunctional n A

@[simp] theorem matrixTraceFunctional_apply (n : ℕ) (A : MatrixStage n) :
    matrixTraceFunctional n A =
      (1 / (2 ^ n : ℂ)) * Matrix.trace A := by
  rfl

@[simp] theorem matrixTraceState_apply (n : ℕ) (A : MatrixStage n) :
    matrixTraceState n A =
      (1 / (2 ^ n : ℂ)) * Matrix.trace A := by
  rfl

/-- **Theorem**: The normalized matrix trace of the identity matrix is 1. -/
theorem matrixTraceState_one (n : ℕ) : matrixTraceState n 1 = 1 := by
  rw [matrixTraceState_apply]
  rw [Matrix.trace_one]
  have h_pos : (2 ^ n : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero n (by norm_num)
  have h_tr : (↑(Fintype.card (Fin (2 ^ n))) : ℂ) = (2 ^ n : ℂ) := by
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [h_tr]
  exact one_div_mul_cancel h_pos

theorem matrixTraceState_mul_comm (n : ℕ)
    (A B : MatrixStage n) :
    matrixTraceState n (A * B) = matrixTraceState n (B * A) := by
  rw [matrixTraceState_apply, matrixTraceState_apply, Matrix.trace_mul_comm]

theorem matrixTraceState_star (n : ℕ) (A : MatrixStage n) :
    star (matrixTraceState n A) = matrixTraceState n (star A) := by
  rw [matrixTraceState_apply, matrixTraceState_apply]
  calc
    star ((1 / (2 ^ n : ℂ)) * Matrix.trace A) =
        star (Matrix.trace A) * star (1 / (2 ^ n : ℂ)) := by
          rw [StarMul.star_mul]
    _ = Matrix.trace (star A) * (1 / (2 ^ n : ℂ)) := by
          rw [← Matrix.trace_conjTranspose A]
          congr 1
          simp only [star_div₀, star_one, star_pow, star_ofNat]
    _ = (1 / (2 ^ n : ℂ)) * Matrix.trace (star A) := by ring

/-- **Theorem**: Trace of star A * A is a non-negative real scalar. -/
theorem matrixTrace_star_mul_self_nonneg (n : ℕ) (A : MatrixStage n) :
    0 ≤ (Matrix.trace (star A * A)).re := by
  dsimp [Matrix.trace, mul_apply, star, conjTranspose_apply]
  have h_elem (k i : Fin (2 ^ n)) : (starRingEnd ℂ (A k i) * A k i).re = Complex.normSq (A k i) := by
    rw [mul_comm, Complex.mul_conj]
    rfl
  have h_sum2 (i : Fin (2 ^ n)) : (∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i).re = ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
    have h_map := map_sum Complex.reAddGroupHom (fun k => starRingEnd ℂ (A k i) * A k i) Finset.univ
    change Complex.reAddGroupHom (∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) = ∑ k : Fin (2 ^ n), Complex.normSq (A k i)
    rw [h_map]
    congr 1; ext k
    exact h_elem k i
  have h_sum1 : (∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i).re = ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
    have h_map := map_sum Complex.reAddGroupHom (fun i => ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) Finset.univ
    change Complex.reAddGroupHom (∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) = ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i)
    rw [h_map]
    congr 1; ext i
    exact h_sum2 i
  rw [h_sum1]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg (A k i)

theorem matrixTrace_star_mul_self_im_zero (n : ℕ) (A : MatrixStage n) :
    (Matrix.trace (star A * A)).im = 0 := by
  have hself : star (star A * A) = star A * A := by
    simp [Matrix.star_mul]
  have hconj : star (Matrix.trace (star A * A)) = Matrix.trace (star A * A) := by
    rw [← Matrix.trace_conjTranspose]
    exact congrArg Matrix.trace hself
  exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using hconj)

/-- The real part of the normalized trace on `A* A` is nonnegative. -/
theorem matrixTraceState_realPart_star_mul_self_nonneg
    (n : ℕ) (A : MatrixStage n) :
    0 ≤ (matrixTraceState n (star A * A)).re := by
  rw [matrixTraceState_apply]
  have h_cast : (1 / (2 ^ n : ℂ)) = ↑(1 / (2 ^ n : ℝ)) := by push_cast; rfl
  have h_c_re : (1 / (2 ^ n : ℂ)).re = 1 / (2 ^ n : ℝ) := by rw [h_cast, Complex.ofReal_re]
  have h_c_im : (1 / (2 ^ n : ℂ)).im = 0 := by rw [h_cast, Complex.ofReal_im]
  rw [Complex.mul_re, h_c_re, h_c_im, zero_mul, sub_zero]
  have h_factor : 0 ≤ 1 / (2 ^ n : ℝ) := by positivity
  exact mul_nonneg h_factor (matrixTrace_star_mul_self_nonneg n A)

end InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
