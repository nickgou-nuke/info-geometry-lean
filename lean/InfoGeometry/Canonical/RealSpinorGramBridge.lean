/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.RealPauliPfaffianKernel
import InfoGeometry.Twistor.SpinorOuterProduct
import Mathlib.Data.Matrix.Block

/-!
# Real spinor Gram matrices in the existing Pauli convention

The real coordinates `(a₁,b₁,a₂,b₂)` use the fixed phase
`J₂ = [[0,-1],[1,0]]`: each spinor block is `a I₂ + b J₂`.
Consequently the second spatial momentum coordinate is
`a₁*b₂ - b₁*a₂`. Replacing `J₂` by its negative reverses that
coordinate convention; no signature is changed here.

The two-constituent interval is a real-coordinate specialization of the
existing `SpinorOuterProduct.det_sum_self_outer` theorem. Its determinant
uses the complex-bilinear alternating minor, without conjugating either
spinor inside the minor. Complex numbers occur only in that proof adapter;
all public definitions and theorem statements below have real carriers.

The final operators are actual eight-dimensional odd blocks on the native
sum index `Fin 4 ⊕ Fin 4`. They give a finite Gram factorization with the
full anticommutator `diag(B Bᵀ, Bᵀ B)`. Concatenating two spinor column pairs
realizes a sum of constituent momenta. Adding their odd operators would
instead introduce mixed Gram terms. No spacetime translation action or
Lorentz super-Poincare representation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealSpinorGramBridge

open scoped Matrix
open InfoGeometry.Canonical.RealPauliPfaffianKernel

/-- Operators on the real phase plane include a quarter-turn and a
reflection that do not commute. The witnesses are the fixed phase
`J₂ = [[0,-1],[1,0]]` and the phase-conjugating reflection `K = diag(1,-1)`,
so the full matrix algebra retains more than the commuting phase-rotation
subalgebra. -/
theorem exists_phase_and_reflection_not_commuting :
    ∃ J K : Matrix (Fin 2) (Fin 2) ℝ,
      J * K ≠ K * J ∧ J * J = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
        K * K = 1 := by
  refine ⟨!![0, -1; 1, 0], Matrix.diagonal ![1, -1], ?_, ?_, ?_⟩
  · intro heq
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) heq
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- A phase-linear spinor column, written as an actual real `4 × 2` matrix. -/
def spinorMatrix (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![u 0, -u 1;
     u 1, u 0;
     u 2, -u 3;
     u 3, u 2]

/-- Coordinates of its Gram matrix in the existing real Pauli basis. -/
def spinorMomentum (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) / 2,
    u 0 * u 2 + u 1 * u 3,
    u 0 * u 3 - u 1 * u 2,
    (u 0 ^ 2 + u 1 ^ 2 - u 2 ^ 2 - u 3 ^ 2) / 2]

/-- The full spinor Gram matrix equals the existing Pauli representative. -/
theorem spinorMatrix_mul_transpose (u : Fin 4 → ℝ) :
    spinorMatrix u * (spinorMatrix u).transpose =
      pauli (spinorMomentum u 0) (spinorMomentum u 1)
        (spinorMomentum u 2) (spinorMomentum u 3) := by
  rw [pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinorMatrix, spinorMomentum, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- The two real columns have equal squared norm and are orthogonal. -/
theorem spinorMatrix_transpose_mul (u : Fin 4 → ℝ) :
    (spinorMatrix u).transpose * spinorMatrix u =
      (2 * spinorMomentum u 0) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinorMatrix, spinorMomentum, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

theorem spinorMomentum_time_nonneg (u : Fin 4 → ℝ) :
    0 ≤ spinorMomentum u 0 := by
  dsimp [spinorMomentum]
  positivity

/-- A single spinor produces a future-directed null-or-zero Pauli vector. -/
theorem spinorMomentum_interval_zero (u : Fin 4 → ℝ) :
    intervalSq (spinorMomentum u 0) (spinorMomentum u 1)
      (spinorMomentum u 2) (spinorMomentum u 3) = 0 := by
  simp [spinorMomentum, intervalSq]
  ring

theorem spinorMomentum_pauli_det_zero (u : Fin 4 → ℝ) :
    (pauli (spinorMomentum u 0) (spinorMomentum u 1)
      (spinorMomentum u 2) (spinorMomentum u 3)).det = 0 := by
  rw [pauli_det, spinorMomentum_interval_zero]
  norm_num

/-- Real and phase coefficients of the alternating two-spinor determinant. -/
def phaseMinor (u v : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![u 0 * v 2 - u 1 * v 3 - u 2 * v 0 + u 3 * v 1,
    u 0 * v 3 + u 1 * v 2 - u 2 * v 1 - u 3 * v 0]

/-- The existing Hermitian-dyad determinant theorem in real Pauli coordinates. -/
theorem two_spinor_interval_eq_minor_normSq (u v : Fin 4 → ℝ) :
    intervalSq (spinorMomentum u 0 + spinorMomentum v 0)
      (spinorMomentum u 1 + spinorMomentum v 1)
      (spinorMomentum u 2 + spinorMomentum v 2)
      (spinorMomentum u 3 + spinorMomentum v 3) =
        phaseMinor u v 0 ^ 2 + phaseMinor u v 1 ^ 2 := by
  let pi : Fin 2 → ℂ := ![⟨u 0, u 1⟩, ⟨u 2, u 3⟩]
  let rho : Fin 2 → ℂ := ![⟨v 0, v 1⟩, ⟨v 2, v 3⟩]
  have h := congrArg Complex.re
    (InfoGeometry.Twistor.SpinorOuterProduct.det_sum_self_outer pi rho)
  convert h using 1 <;>
    simp [spinorMomentum, phaseMinor, intervalSq, pi, rho,
      Matrix.det_fin_two, Matrix.vecMulVec, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem two_spinor_interval_nonneg (u v : Fin 4 → ℝ) :
    0 ≤ intervalSq (spinorMomentum u 0 + spinorMomentum v 0)
      (spinorMomentum u 1 + spinorMomentum v 1)
      (spinorMomentum u 2 + spinorMomentum v 2)
      (spinorMomentum u 3 + spinorMomentum v 3) := by
  rw [two_spinor_interval_eq_minor_normSq]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Strict timelikeness requires a nonzero phase-linear determinant. -/
theorem two_spinor_interval_pos_iff (u v : Fin 4 → ℝ) :
    0 < intervalSq (spinorMomentum u 0 + spinorMomentum v 0)
      (spinorMomentum u 1 + spinorMomentum v 1)
      (spinorMomentum u 2 + spinorMomentum v 2)
      (spinorMomentum u 3 + spinorMomentum v 3) ↔ phaseMinor u v ≠ 0 := by
  rw [two_spinor_interval_eq_minor_normSq]
  constructor
  · intro h hz
    simp [hz] at h
  · intro h
    by_cases h0 : phaseMinor u v 0 = 0
    · have h1 : phaseMinor u v 1 ≠ 0 := by
        intro h1
        apply h
        funext i
        fin_cases i
        · exact h0
        · exact h1
      simpa [h0] using (sq_pos_iff.mpr h1)
    · exact add_pos_of_pos_of_nonneg (sq_pos_iff.mpr h0) (sq_nonneg _)

/-- Concatenate two real spinor column pairs, retaining constituent labels. -/
def spinorPairMatrix (u v : Fin 4 → ℝ) : Matrix4 :=
  !![u 0, -u 1, v 0, -v 1;
     u 1, u 0, v 1, v 0;
     u 2, -u 3, v 2, -v 3;
     u 3, u 2, v 3, v 2]

/-- The determinant of the actual spinor column matrix is the nonnegative interval
of the constituent sum, by `two_spinor_interval_eq_minor_normSq`.
The interleaved orientation gives a positive sign: the basis spinor columns
concatenate to the identity matrix. -/
theorem spinorPairMatrix_det (u v : Fin 4 → ℝ) :
    (spinorPairMatrix u v).det =
      phaseMinor u v 0 ^ 2 + phaseMinor u v 1 ^ 2 := by
  simp [spinorPairMatrix, phaseMinor, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove, pow_two]
  ring

theorem spinorPairMatrix_gram (u v : Fin 4 → ℝ) :
    spinorPairMatrix u v * (spinorPairMatrix u v).transpose =
      spinorMatrix u * (spinorMatrix u).transpose +
        spinorMatrix v * (spinorMatrix v).transpose := by
  simp only [spinorMatrix_mul_transpose, pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinorPairMatrix, spinorMomentum, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

theorem spinorPairMatrix_gram_eq_pauli (u v : Fin 4 → ℝ) :
    spinorPairMatrix u v * (spinorPairMatrix u v).transpose =
      pauli (spinorMomentum u 0 + spinorMomentum v 0)
        (spinorMomentum u 1 + spinorMomentum v 1)
        (spinorMomentum u 2 + spinorMomentum v 2)
        (spinorMomentum u 3 + spinorMomentum v 3) := by
  rw [spinorPairMatrix_gram, spinorMatrix_mul_transpose,
    spinorMatrix_mul_transpose]
  unfold pauli
  module

/-- Upper odd block on two four-dimensional real summands. -/
def oddUpper (B : Matrix4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks 0 B 0 0

/-- Its real adjoint is the corresponding lower odd block. -/
def oddLower (B : Matrix4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks 0 0 B.transpose 0

theorem oddUpper_transpose (B : Matrix4) :
    (oddUpper B).transpose = oddLower B := by
  simp [oddUpper, oddLower, Matrix.fromBlocks_transpose]

theorem oddUpper_sq_zero (B : Matrix4) : oddUpper B * oddUpper B = 0 := by
  simp [oddUpper, Matrix.fromBlocks_multiply]

theorem oddLower_sq_zero (B : Matrix4) : oddLower B * oddLower B = 0 := by
  simp [oddLower, Matrix.fromBlocks_multiply]

/-- Full finite anticommutator, retaining both generally different Gram blocks. -/
theorem odd_anticommutator (B : Matrix4) :
    oddUpper B * oddLower B + oddLower B * oddUpper B =
      Matrix.fromBlocks (B * B.transpose) 0 0 (B.transpose * B) := by
  simp [oddUpper, oddLower, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

/-- A genuine two-constituent Gram sum occurs in the upper even block. -/
theorem pair_odd_anticommutator (u v : Fin 4 → ℝ) :
    oddUpper (spinorPairMatrix u v) * oddLower (spinorPairMatrix u v) +
        oddLower (spinorPairMatrix u v) * oddUpper (spinorPairMatrix u v) =
      Matrix.fromBlocks
        (pauli (spinorMomentum u 0 + spinorMomentum v 0)
          (spinorMomentum u 1 + spinorMomentum v 1)
          (spinorMomentum u 2 + spinorMomentum v 2)
          (spinorMomentum u 3 + spinorMomentum v 3)) 0 0
        ((spinorPairMatrix u v).transpose * spinorPairMatrix u v) := by
  rw [odd_anticommutator, spinorPairMatrix_gram_eq_pauli]

/-- Padding one spinor with zero gives its null Pauli Gram in the upper block. -/
theorem single_odd_anticommutator (u : Fin 4 → ℝ) :
    oddUpper (spinorPairMatrix u 0) * oddLower (spinorPairMatrix u 0) +
        oddLower (spinorPairMatrix u 0) * oddUpper (spinorPairMatrix u 0) =
      Matrix.fromBlocks
        (pauli (spinorMomentum u 0) (spinorMomentum u 1)
          (spinorMomentum u 2) (spinorMomentum u 3)) 0 0
        ((spinorPairMatrix u 0).transpose * spinorPairMatrix u 0) := by
  simpa [spinorMomentum] using pair_odd_anticommutator u 0

end InfoGeometry.Canonical.RealSpinorGramBridge

end
