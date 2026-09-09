import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import InfoGeometry.Clifford.DiracPauliGamma

/-! The associative product on the existing finite Dirac carrier splits into
its symmetric Jordan channel and antisymmetric Lie channel. -/

noncomputable section

namespace InfoGeometry.Canonical.OperatorHermitianLieJordanSplit

open InfoGeometry.Clifford.DiracPauliGamma

def operatorJordanProduct (A B : DiracMatrix) : DiracMatrix :=
  (2 : ℂ)⁻¹ • (A * B + B * A)

def operatorLieBracket (A B : DiracMatrix) : DiracMatrix := A * B - B * A

theorem operator_product_eq_jordan_add_half_lie (A B : DiracMatrix) :
    A * B = operatorJordanProduct A B +
      (2 : ℂ)⁻¹ • operatorLieBracket A B := by
  unfold operatorJordanProduct operatorLieBracket
  module

theorem operatorJordanProduct_comm (A B : DiracMatrix) :
    operatorJordanProduct A B = operatorJordanProduct B A := by
  simp [operatorJordanProduct, add_comm]

theorem operatorLieBracket_swap (A B : DiracMatrix) :
    operatorLieBracket B A = -operatorLieBracket A B := by
  simp [operatorLieBracket]

theorem operatorJordanProduct_isHermitian {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (operatorJordanProduct A B).IsHermitian := by
  rw [Matrix.IsHermitian] at hA hB ⊢
  simp [operatorJordanProduct, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA, hB, add_comm]

theorem operatorLieBracket_conjTranspose {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.conjTranspose (operatorLieBracket A B) =
      -operatorLieBracket A B := by
  rw [Matrix.IsHermitian] at hA hB
  simp [operatorLieBracket, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hA, hB]

theorem I_smul_operatorLieBracket_isHermitian {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Complex.I • operatorLieBracket A B).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul,
    operatorLieBracket_conjTranspose hA hB]
  simp

theorem hermitian_product_lie_jordan_packet {A B : DiracMatrix}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A * B = operatorJordanProduct A B +
        (2 : ℂ)⁻¹ • operatorLieBracket A B ∧
      (operatorJordanProduct A B).IsHermitian ∧
      Matrix.conjTranspose (operatorLieBracket A B) =
        -operatorLieBracket A B := by
  exact ⟨operator_product_eq_jordan_add_half_lie A B,
    operatorJordanProduct_isHermitian hA hB,
    operatorLieBracket_conjTranspose hA hB⟩

end InfoGeometry.Canonical.OperatorHermitianLieJordanSplit
