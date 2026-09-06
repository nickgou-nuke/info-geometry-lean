import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import InfoGeometry.Clifford.DiracPauliGamma

/-!
# InfoGeometry.Canonical.OperatorHermitianLieJordanSplit

Canonical symmetric/antisymmetric split of products of finite Dirac-matrix
operators.

For Hermitian `A,B`, the symmetric product

`A ∘ B = 1/2 (AB + BA)`

is Hermitian, while the commutator

`[A,B] = AB - BA`

is skew-Hermitian.  Thus the associative product decomposes exactly into a
Jordan observable channel and a Lie/derivation channel:

`AB = A ∘ B + 1/2 [A,B]`.

This is a finite matrix statement.  No claim that every skew-Hermitian matrix
is a geometric gauge connection is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorHermitianLieJordanSplit

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma

/-- Symmetrized Jordan product on the existing finite Dirac matrix carrier. -/
def operatorJordanProduct (A B : DiracMatrix) : DiracMatrix :=
  (2 : ℂ)⁻¹ • (A * B + B * A)

/-- Antisymmetrized Lie channel on the same associative carrier. -/
def operatorLieBracket (A B : DiracMatrix) : DiracMatrix :=
  A * B - B * A

/-- Exact reconstruction of the associative product from its Jordan and Lie
channels. -/
theorem operator_product_eq_jordan_add_half_lie
    (A B : DiracMatrix) :
    A * B =
      operatorJordanProduct A B +
        (2 : ℂ)⁻¹ • operatorLieBracket A B := by
  unfold operatorJordanProduct operatorLieBracket
  module

/-- Swapping the factors preserves the Jordan channel. -/
theorem operatorJordanProduct_comm (A B : DiracMatrix) :
    operatorJordanProduct A B = operatorJordanProduct B A := by
  simp [operatorJordanProduct, add_comm]

/-- Swapping the factors negates the Lie channel. -/
theorem operatorLieBracket_swap (A B : DiracMatrix) :
    operatorLieBracket B A = -operatorLieBracket A B := by
  simp [operatorLieBracket]
  abel

/-- The Jordan product of Hermitian operators remains Hermitian. -/
theorem operatorJordanProduct_isHermitian
    {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (operatorJordanProduct A B).IsHermitian := by
  rw [Matrix.IsHermitian] at hA hB ⊢
  simp [operatorJordanProduct, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA, hB,
    add_comm]

/-- The commutator of Hermitian operators is skew-Hermitian. -/
theorem operatorLieBracket_conjTranspose
    {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.conjTranspose (operatorLieBracket A B) =
      -operatorLieBracket A B := by
  rw [Matrix.IsHermitian] at hA hB
  simp [operatorLieBracket, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hA, hB]

/-- Multiplying the skew-Hermitian commutator by `i` returns a Hermitian
observable. -/
theorem I_smul_operatorLieBracket_isHermitian
    {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Complex.I • operatorLieBracket A B).IsHermitian := by
  rw [Matrix.IsHermitian]
  rw [Matrix.conjTranspose_smul,
    operatorLieBracket_conjTranspose hA hB]
  simp

/-- The product decomposition together with the adjoint parity of the two
channels. -/
theorem hermitian_product_lie_jordan_packet
    {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A * B =
        operatorJordanProduct A B +
          (2 : ℂ)⁻¹ • operatorLieBracket A B ∧
      (operatorJordanProduct A B).IsHermitian ∧
      Matrix.conjTranspose (operatorLieBracket A B) =
        -operatorLieBracket A B := by
  exact ⟨operator_product_eq_jordan_add_half_lie A B,
    operatorJordanProduct_isHermitian hA hB,
    operatorLieBracket_conjTranspose hA hB⟩

end InfoGeometry.Canonical.OperatorHermitianLieJordanSplit
