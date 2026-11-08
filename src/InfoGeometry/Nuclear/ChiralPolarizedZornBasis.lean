import InfoGeometry.Nuclear.WaleckaZornBdG

namespace InfoGeometry.Nuclear.ChiralPolarizedZornBasis

open InfoGeometry.Algebra
open InfoGeometry.Nuclear.NambuGorkov
open InfoGeometry.Nuclear.WaleckaZornBdG
open InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge

noncomputable section

theorem diagonal_offDiagonal_anticommutator
    {Scalar : Type*} [CommRing Scalar] (left right : Scalar)
    (upper lower : ZornVec3 Scalar) :
    ZornVectorMatrix.mul (ZornVectorMatrix.diagonal left right)
        (ZornVectorMatrix.offDiagonal upper lower) +
      ZornVectorMatrix.mul (ZornVectorMatrix.offDiagonal upper lower)
        (ZornVectorMatrix.diagonal left right) =
      (left + right) • ZornVectorMatrix.offDiagonal upper lower := by
  rw [ZornVectorMatrix.diagonal_mul, ZornVectorMatrix.mul_diagonal]
  ext coordinate <;> simp [ZornVectorMatrix.offDiagonal] <;> ring

theorem mass_gap_cross_terms_zero
    {Scalar : Type*} [CommRing Scalar] (mass : Scalar)
    (upper lower : ZornVec3 Scalar) :
    ZornVectorMatrix.mul (ZornVectorMatrix.diagonal mass (-mass))
        (ZornVectorMatrix.offDiagonal upper lower) +
      ZornVectorMatrix.mul (ZornVectorMatrix.offDiagonal upper lower)
        (ZornVectorMatrix.diagonal mass (-mass)) = 0 := by
  rw [diagonal_offDiagonal_anticommutator, add_neg_cancel, zero_smul]

theorem offDiagonal_square
    {Scalar : Type*} [CommRing Scalar] (upper lower : ZornVec3 Scalar) :
    ZornVectorMatrix.mul (ZornVectorMatrix.offDiagonal upper lower)
        (ZornVectorMatrix.offDiagonal upper lower) =
      ZornVectorMatrix.scalar (ZornVec3.dot upper lower) := by
  ext coordinate <;>
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.scalar, ZornVec3.dot_comm]

theorem nativeHamiltonian_polarized_decomposition (state : NambuGorkovCarrier ℝ) :
    nativeHamiltonian state =
      ZornVectorMatrix.diagonal state.xi (-state.xi) +
        ZornVectorMatrix.offDiagonal state.delta state.delta := by
  ext coordinate <;>
    simp [nativeHamiltonian, oldToVector, toZorn,
      ZornVectorMatrix.diagonal, ZornVectorMatrix.offDiagonal]

theorem identity_anticommutator (element : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.mul ZornVectorMatrix.one element +
      ZornVectorMatrix.mul element ZornVectorMatrix.one = (2 : ℝ) • element := by
  rw [ZornVectorMatrix.one_mul, ZornVectorMatrix.mul_one]
  exact (two_smul ℝ element).symm

theorem identity_anticommutator_ne_zero (element : ZornVectorMatrix ℝ)
    (nonzero : element ≠ 0) :
    ZornVectorMatrix.mul ZornVectorMatrix.one element +
      ZornVectorMatrix.mul element ZornVectorMatrix.one ≠ 0 := by
  rw [identity_anticommutator]
  exact smul_ne_zero (by norm_num) nonzero

end

end InfoGeometry.Nuclear.ChiralPolarizedZornBasis
