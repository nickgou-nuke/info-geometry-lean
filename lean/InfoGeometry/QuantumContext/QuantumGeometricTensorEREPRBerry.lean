/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Section 119: Finite Matrix Symmetric–Skew Orthogonal Decomposition and Gram/Determinant Identities

This module proves finite algebraic identities for a four-coordinate matrix carrier `Cl11Op R`:
1. The doubled symmetric (`Q + Qᵀ`) and skew-symmetric (`Q - Qᵀ`) parts reconstruct `2 Q`,
   are orthogonal under the Frobenius inner product (`⟨Q + Qᵀ, Q - Qᵀ⟩_HS = 0`), and satisfy
   the Pythagorean Frobenius norm partition `‖Q + Qᵀ‖²_HS + ‖Q - Qᵀ‖²_HS = 4 ‖Q‖²_HS`.
2. Multiplication `Cl11Op.mul` is non-commutative over `ℤ`, satisfies `frobeniusPairing A B = trace (mul (transpose A) B)`,
   and satisfies determinant multiplicativity `det (mul A B) = det A * det B`.
3. Under the indefinite bilinear form `metricBracket`, any symmetric off-diagonal tunneling
   operator `H = [[0, h], [h, 0]]` and diagonal operator `S = [[s₁, 0], [0, s₂]]` are orthogonal (`⟨H, S⟩ = 0`).
4. For the off-diagonal Weyl operator `W = [[0, γ_L], [γ_R, 0]]`, its square is diagonal
   `W² = diag(γ_L γ_R, γ_L γ_R)` with trace `Tr(W²) = 2 γ_L γ_R = -2 det(W)`.
-/

namespace InfoGeometry.QuantumContext.QGTBerryEREPR

variable {R : Type*} [CommRing R]

/-! ## Section 1: $\mathrm{Cl}(1,1)$ Operator Carrier and Frobenius Inner Product (`Cl11Op R`) -/

/-- Four-coordinate record with matrix-shaped operations. -/
@[ext]
structure Cl11Op (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R
  deriving DecidableEq, Repr, Inhabited

namespace Cl11Op

variable {R : Type*} [CommRing R]

/-- Zero $\mathrm{Cl}(1,1)$ operator. -/
def zero : Cl11Op R := ⟨0, 0, 0, 0⟩

/-- Canonical non-zero integer $\mathrm{Cl}(1,1)$ operator. -/
def canonicalOp : Cl11Op ℤ := ⟨1, 2, -2, 1⟩

/-- The canonical operator `canonicalOp` over $\mathbb{Z}$ is distinct from `zero`. -/
theorem canonicalOp_ne_zero : canonicalOp ≠ (zero : Cl11Op ℤ) := by
  intro h
  have h1 : canonicalOp.m11 = (zero : Cl11Op ℤ).m11 := congrArg Cl11Op.m11 h
  revert h1
  decide

/-- Entrywise addition of $\mathrm{Cl}(1,1)$ operators. -/
def add (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

/-- Scalar multiplication of a $\mathrm{Cl}(1,1)$ operator. -/
def smul (c : R) (A : Cl11Op R) : Cl11Op R :=
  ⟨c * A.m11, c * A.m12, c * A.m21, c * A.m22⟩

/-- Two-by-two matrix multiplication of $\mathrm{Cl}(1,1)$ operators. -/
def mul (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21,
   A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21,
   A.m21 * B.m12 + A.m22 * B.m22⟩

/-- Non-commutativity of `Cl11Op.mul` over $\mathbb{Z}$. -/
theorem mul_noncommutative_int :
    let A : Cl11Op ℤ := ⟨1, 1, 0, 1⟩
    let B : Cl11Op ℤ := ⟨1, 0, 1, 1⟩
    mul A B ≠ mul B A := by
  decide

/-- Matrix transpose $A^\top$. -/
def transpose (A : Cl11Op R) : Cl11Op R :=
  ⟨A.m11, A.m21, A.m12, A.m22⟩

/-- Matrix trace $\operatorname{Tr}(A) = m_{11} + m_{22}$. -/
def trace (A : Cl11Op R) : R :=
  A.m11 + A.m22

/-- Matrix determinant $\det(A) = m_{11} m_{22} - m_{12} m_{21}$. -/
def det (A : Cl11Op R) : R :=
  A.m11 * A.m22 - A.m12 * A.m21

/-- Coordinate Frobenius pairing $\langle A, B \rangle_{\mathrm{HS}} = \operatorname{Tr}(A^\top B)$. -/
def frobeniusPairing (A B : Cl11Op R) : R :=
  A.m11 * B.m11 + A.m12 * B.m12 + A.m21 * B.m21 + A.m22 * B.m22

/-- Equivalence between `frobeniusPairing A B` and `trace (mul (transpose A) B)`. -/
theorem frobeniusPairing_eq_trace_transpose_mul (A B : Cl11Op R) :
    frobeniusPairing A B = trace (mul (transpose A) B) := by
  dsimp [frobeniusPairing, trace, mul, transpose]
  ring

/-- Multiplicativity of the determinant: $\det(A B) = \det(A) \det(B)$. -/
theorem det_mul (A B : Cl11Op R) :
    det (mul A B) = det A * det B := by
  dsimp [det, mul]
  ring

/-! ## Section 2: Symmetric and Skew-Symmetric Coordinate Parts -/

/-- Doubled symmetric coordinate part, $Q+Q^\top$. -/
def symmetricPartTwice (Q : Cl11Op R) : Cl11Op R :=
  ⟨2 * Q.m11, Q.m12 + Q.m21, Q.m12 + Q.m21, 2 * Q.m22⟩

/-- Doubled skew-symmetric coordinate part, $Q-Q^\top$. -/
def skewPartTwice (Q : Cl11Op R) : Cl11Op R :=
  ⟨0, Q.m12 - Q.m21, Q.m21 - Q.m12, 0⟩

/-- The symmetric coordinate part is invariant under transposition. -/
@[simp]
theorem symmetricPartTwice_is_symmetric (Q : Cl11Op R) :
    transpose (symmetricPartTwice Q) = symmetricPartTwice Q := by
  simp [transpose, symmetricPartTwice]

/-- The symmetric and skew coordinate parts sum to twice the original record. -/
theorem symmetric_add_skew_eq_two_smul (Q : Cl11Op R) :
    add (symmetricPartTwice Q) (skewPartTwice Q) = smul 2 Q := by
  ext <;> dsimp [add, symmetricPartTwice, skewPartTwice, smul] <;> ring

/-- The Frobenius coordinate pairing of the symmetric and skew parts vanishes. -/
theorem symmetric_skew_frobenius_pairing_zero (Q : Cl11Op R) :
    frobeniusPairing (symmetricPartTwice Q) (skewPartTwice Q) = 0 := by
  dsimp [frobeniusPairing, symmetricPartTwice, skewPartTwice]
  ring

/-- Pythagorean Frobenius norm partition of a matrix into its symmetric and skew parts:
    $\|Q + Q^\top\|_{\mathrm{HS}}^2 + \|Q - Q^\top\|_{\mathrm{HS}}^2 = 4 \|Q\|_{\mathrm{HS}}^2$. -/
theorem symmetric_skew_pythagorean_frobenius_norm (Q : Cl11Op R) :
    frobeniusPairing (symmetricPartTwice Q) (symmetricPartTwice Q) +
      frobeniusPairing (skewPartTwice Q) (skewPartTwice Q) =
    4 * frobeniusPairing Q Q := by
  dsimp [frobeniusPairing, symmetricPartTwice, skewPartTwice]
  ring

/-! ## Section 3: Restricted Cross-Pairing Nullity ($\langle H, S \rangle = 0$) -/

/-- Symmetric bilinear form $\langle A, B \rangle$ on the real matrix carrier. It is
    indefinite, and is not a positive dissipative bracket. -/
def metricBracket (A B : Cl11Op R) : R :=
  (A.m12 - A.m21) * (B.m12 - B.m21) - (A.m11 * B.m22 + A.m22 * B.m11)

/-- The symmetric form takes both signs on real matrices. -/
theorem metricBracket_indefinite_over_reals :
    metricBracket (⟨1, 0, 0, 1⟩ : Cl11Op ℝ)
        (⟨1, 0, 0, 1⟩ : Cl11Op ℝ) = -2 ∧
      metricBracket (⟨0, 1, 0, 0⟩ : Cl11Op ℝ)
        (⟨0, 1, 0, 0⟩ : Cl11Op ℝ) = 1 := by
  norm_num [metricBracket]

/-- The real form therefore fails positive semidefiniteness. -/
theorem metricBracket_not_positiveSemidefinite :
    ¬ ∀ A : Cl11Op ℝ, 0 ≤ metricBracket A A := by
  intro h
  have hId := h (⟨1, 0, 0, 1⟩ : Cl11Op ℝ)
  norm_num [metricBracket] at hId

/-- Restricted Cross-Pairing Nullity ($\langle H, S \rangle = 0$):
    For a symmetric inter-sheet tunneling Hamiltonian $H = \begin{pmatrix} 0 & h \\ h & 0 \end{pmatrix}$
    and a diagonal shell entropy operator $S = \begin{pmatrix} s_1 & 0 \\ 0 & s_2 \end{pmatrix}$,
    their cross-pairing under the symmetric form vanishes identically. -/
theorem cross_metric_bracket_hamiltonian_entropy_zero (h s₁ s₂ : R) :
    let H : Cl11Op R := ⟨0, h, h, 0⟩
    let S : Cl11Op R := ⟨s₁, 0, 0, s₂⟩
    metricBracket H S = 0 := by
  dsimp [metricBracket]
  ring

/-! ## Section 4: Off-Diagonal Square Trace and Determinant Relation -/

/-- Off-diagonal Weyl bridge matrix $W(\gamma_L, \gamma_R) = \begin{pmatrix} 0 & \gamma_L \\ \gamma_R & 0 \end{pmatrix}$. -/
def offDiagonalMatrix (γ_L γ_R : R) : Cl11Op R :=
  ⟨0, γ_L, γ_R, 0⟩

/-- Negative determinant of the off-diagonal matrix: $-\det(W(\gamma_L, \gamma_R))$. -/
def negativeDeterminant (γ_L γ_R : R) : R :=
  - det (offDiagonalMatrix γ_L γ_R)

/-- Spectral trace of the squared off-diagonal matrix $\operatorname{Tr}(W(\gamma_L, \gamma_R)^2)$. -/
def twiceOffDiagonalProduct (γ_L γ_R : R) : R :=
  trace (mul (offDiagonalMatrix γ_L γ_R) (offDiagonalMatrix γ_L γ_R))

/-- The square of the off-diagonal Weyl matrix is scalar diagonal:
    $W(\gamma_L, \gamma_R)^2 = \operatorname{diag}(\gamma_L \gamma_R, \gamma_L \gamma_R)$. -/
theorem offDiagonalMatrix_sq_diagonal (γ_L γ_R : R) :
    mul (offDiagonalMatrix γ_L γ_R) (offDiagonalMatrix γ_L γ_R) =
      ⟨γ_L * γ_R, 0, 0, γ_L * γ_R⟩ := by
  ext <;> dsimp [mul, offDiagonalMatrix] <;> ring

/-- The trace of the squared off-diagonal matrix equals twice its negative determinant
    and equals $2 \gamma_L \gamma_R$:
    $\operatorname{Tr}(W^2) = 2 (-\det W) = 2 \gamma_L \gamma_R$. -/
theorem offDiagonalDeterminant_identity (γ_L γ_R : R) :
    twiceOffDiagonalProduct γ_L γ_R = 2 * negativeDeterminant γ_L γ_R ∧
    twiceOffDiagonalProduct γ_L γ_R = 2 * (γ_L * γ_R) := by
  dsimp [twiceOffDiagonalProduct, negativeDeterminant, trace, mul, det, offDiagonalMatrix]
  exact ⟨by ring, by ring⟩

/-- For a chiral nilpotent off-diagonal matrix ($\gamma_L = 0$), its square is the zero matrix
    Even when $\gamma_R \ne 0$, while $W(0, \gamma_R)$ itself has entry $m_{21} = \gamma_R$. -/
theorem offDiagonalMatrix_nilpotent_left_zero (γ_R : R) :
    (offDiagonalMatrix 0 γ_R).m21 = γ_R ∧
    mul (offDiagonalMatrix 0 γ_R) (offDiagonalMatrix 0 γ_R) = zero ∧
    negativeDeterminant 0 γ_R = 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · ext <;> dsimp [mul, offDiagonalMatrix, zero] <;> ring
  · dsimp [negativeDeterminant, det, offDiagonalMatrix]
    ring

end Cl11Op

/-! ## Section 5: Bundle of Finite Matrix Identities -/
theorem finite_matrix_identity_bundle :
    (∀ Q : Cl11Op R,
      Cl11Op.frobeniusPairing (Cl11Op.symmetricPartTwice Q) (Cl11Op.skewPartTwice Q) = 0) ∧
    (∀ Q : Cl11Op R,
      Cl11Op.frobeniusPairing (Cl11Op.symmetricPartTwice Q) (Cl11Op.symmetricPartTwice Q) +
        Cl11Op.frobeniusPairing (Cl11Op.skewPartTwice Q) (Cl11Op.skewPartTwice Q) =
      4 * Cl11Op.frobeniusPairing Q Q) ∧
    (∀ h s₁ s₂ : R, Cl11Op.metricBracket ⟨0, h, h, 0⟩ ⟨s₁, 0, 0, s₂⟩ = 0) ∧
    (∀ γ_L γ_R : R,
      Cl11Op.twiceOffDiagonalProduct γ_L γ_R = 2 * Cl11Op.negativeDeterminant γ_L γ_R) := by
  exact ⟨Cl11Op.symmetric_skew_frobenius_pairing_zero,
    Cl11Op.symmetric_skew_pythagorean_frobenius_norm,
    Cl11Op.cross_metric_bracket_hamiltonian_entropy_zero,
    fun γ_L γ_R => (Cl11Op.offDiagonalDeterminant_identity γ_L γ_R).1⟩

end InfoGeometry.QuantumContext.QGTBerryEREPR
