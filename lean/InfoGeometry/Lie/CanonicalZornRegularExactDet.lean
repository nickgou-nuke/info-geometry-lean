/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularNorm
import InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact determinant of the canonical Zorn left action

The existing Cartesian coordinates are `(a, x₀, x₁, x₂, b, y₀, y₁, y₂)`.
The two four-by-four off-diagonal blocks have product `(x · y) I`.
A triangular block multiplier computes the determinant when the first scalar
is nonzero; an invertible signed block exchange handles its zero case.
The proof uses finite matrix algebra and includes the entire null cone.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornRegularExactDet

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge

private def cartesianMatrix (Z : ZornMatrix ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  !![Z.a, 0, 0, 0, 0, Z.x 0, Z.x 1, Z.x 2;
     0, Z.a, 0, 0, Z.x 0, 0, Z.y 2, -Z.y 1;
     0, 0, Z.a, 0, Z.x 1, -Z.y 2, 0, Z.y 0;
     0, 0, 0, Z.a, Z.x 2, Z.y 1, -Z.y 0, 0;
     0, Z.y 0, Z.y 1, Z.y 2, Z.b, 0, 0, 0;
     Z.y 0, 0, -Z.x 2, Z.x 1, 0, Z.b, 0, 0;
     Z.y 1, Z.x 2, 0, -Z.x 0, 0, 0, Z.b, 0;
     Z.y 2, -Z.x 1, Z.x 0, 0, 0, 0, 0, Z.b]

/-- The actual left regular matrix in the existing Cartesian coordinate
order `(a, x₀, x₁, x₂, b, y₀, y₁, y₂)`. -/
theorem leftRegular_cartesian_matrix (Z : ZornMatrix ℝ) :
    LinearMap.toMatrix
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        (leftRegularRepresentation Z) =
      !![Z.a, 0, 0, 0, 0, Z.x 0, Z.x 1, Z.x 2;
         0, Z.a, 0, 0, Z.x 0, 0, Z.y 2, -Z.y 1;
         0, 0, Z.a, 0, Z.x 1, -Z.y 2, 0, Z.y 0;
         0, 0, 0, Z.a, Z.x 2, Z.y 1, -Z.y 0, 0;
         0, Z.y 0, Z.y 1, Z.y 2, Z.b, 0, 0, 0;
         Z.y 0, 0, -Z.x 2, Z.x 1, 0, Z.b, 0, 0;
         Z.y 1, Z.x 2, 0, -Z.x 0, 0, 0, Z.b, 0;
         Z.y 2, -Z.x 1, Z.x 0, 0, 0, 0, 0, Z.b] := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right,
    LinearMap.toMatrix_eq_toMatrix']
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  ext v i
  fin_cases i <;>
    simp [LinearMap.comp_apply, canonicalToCoord,
      leftRegularRepresentation, leftMultiplication, ZornMatrix.mul,
      ZornMatrix.dot, ZornMatrix.cross, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;> ring

/-- The actual upper and lower chiral left actions give a noncommuting pair
in the same eight-dimensional Cartesian matrix representation. -/
theorem cartesian_left_actions_noncommuting :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ,
      A * B ≠ B * A ∧
      A = LinearMap.toMatrix
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        (leftRegularRepresentation (ZornMatrix.chiralUpperBasis (R := ℝ) 0)) ∧
      B = LinearMap.toMatrix
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
        (leftRegularRepresentation (ZornMatrix.chiralLowerBasis (R := ℝ) 0)) := by
  refine ⟨cartesianMatrix (ZornMatrix.chiralUpperBasis (R := ℝ) 0),
    cartesianMatrix (ZornMatrix.chiralLowerBasis (R := ℝ) 0), ?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 0 0) h
    norm_num [cartesianMatrix, Matrix.mul_apply, Fin.sum_univ_eight,
      ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis, Pi.single_apply] at h00
  · exact (leftRegular_cartesian_matrix _).symm
  · exact (leftRegular_cartesian_matrix _).symm

private def upperBlock (Z : ZornMatrix ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, Z.x 0, Z.x 1, Z.x 2;
     Z.x 0, 0, Z.y 2, -Z.y 1;
     Z.x 1, -Z.y 2, 0, Z.y 0;
     Z.x 2, Z.y 1, -Z.y 0, 0]

private def lowerBlock (Z : ZornMatrix ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, Z.y 0, Z.y 1, Z.y 2;
     Z.y 0, 0, -Z.x 2, Z.x 1;
     Z.y 1, Z.x 2, 0, -Z.x 0;
     Z.y 2, -Z.x 1, Z.x 0, 0]

private theorem lower_mul_upper (Z : ZornMatrix ℝ) :
    lowerBlock Z * upperBlock Z = ZornMatrix.dot Z.x Z.y • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerBlock, upperBlock, Matrix.mul_apply, Fin.sum_univ_four,
      ZornMatrix.dot, Matrix.one_apply] <;> ring

private theorem cartesianMatrix_blocks (Z : ZornMatrix ℝ) :
    (cartesianMatrix Z).submatrix
        (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8) finSumFinEquiv =
      Matrix.fromBlocks (Z.a • 1) (upperBlock Z) (lowerBlock Z) (Z.b • 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [cartesianMatrix, upperBlock, lowerBlock, Matrix.submatrix_apply,
      Matrix.fromBlocks, Matrix.one_apply, finSumFinEquiv]

/-- Two actual chiral upper blocks retain noncommutativity on the real
four-dimensional block carrier used in the determinant argument. -/
theorem cartesian_upper_blocks_noncommuting :
    ∃ B C : Matrix (Fin 4) (Fin 4) ℝ,
      B * C ≠ C * B ∧
      B = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] ∧
      C = !![0, 0, 1, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0] := by
  refine ⟨upperBlock (ZornMatrix.chiralUpperBasis (R := ℝ) 0),
    upperBlock (ZornMatrix.chiralUpperBasis (R := ℝ) 1), ?_, ?_, ?_⟩
  · intro h
    have h12 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 1 2) h
    norm_num [upperBlock, Matrix.mul_apply, Fin.sum_univ_four,
      ZornMatrix.chiralUpperBasis, Pi.single_apply] at h12
  · norm_num [upperBlock, ZornMatrix.chiralUpperBasis, Pi.single_apply]
  · norm_num [upperBlock, ZornMatrix.chiralUpperBasis, Pi.single_apply]

private theorem det_signed_exchange :
    Matrix.det (Matrix.fromBlocks (0 : Matrix (Fin 4) (Fin 4) ℝ) (-1) 1 0) = 1 := by
  have hfactor :
      Matrix.fromBlocks (0 : Matrix (Fin 4) (Fin 4) ℝ) (-1) 1 0 =
        Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) ℝ) (-1) 1 0 *
          Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 1 1 := by
    simp [Matrix.fromBlocks_multiply]
  rw [hfactor, Matrix.det_mul, Matrix.det_fromBlocks_one₁₁,
    Matrix.det_fromBlocks_zero₁₂]
  simp

private theorem det_scalar_blocks (a b s : ℝ)
    (B C : Matrix (Fin 4) (Fin 4) ℝ) (hCB : C * B = s • 1) :
    Matrix.det (Matrix.fromBlocks (a • 1) B C (b • 1)) = (a * b - s) ^ 4 := by
  by_cases ha : a = 0
  · subst a
    have hproduct :
        Matrix.fromBlocks (0 : Matrix (Fin 4) (Fin 4) ℝ) (-1) 1 0 *
            Matrix.fromBlocks (0 : Matrix (Fin 4) (Fin 4) ℝ) B C (b • 1) =
          Matrix.fromBlocks (-C) (-(b • 1)) 0 B := by
      simp [Matrix.fromBlocks_multiply]
    have hdet := congrArg Matrix.det hproduct
    rw [Matrix.det_mul, det_signed_exchange, one_mul,
      Matrix.det_fromBlocks_zero₂₁, ← Matrix.det_mul, Matrix.neg_mul, hCB] at hdet
    simpa [Matrix.det_neg, Matrix.det_smul] using hdet
  · have hproduct :
        Matrix.fromBlocks (a • 1) B C (b • 1) *
            Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) ℝ) (-B) 0 (a • 1) =
          Matrix.fromBlocks (a • 1) 0 C ((a * b - s) • 1) := by
      simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, hCB]
      rw [neg_add_cancel, mul_comm b a, ← sub_eq_neg_add, ← sub_smul]
    have hdet := congrArg Matrix.det hproduct
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_fromBlocks_zero₁₂] at hdet
    simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
      mul_one, one_mul] at hdet
    apply mul_left_cancel₀ (pow_ne_zero 4 ha)
    simpa only [mul_comm (Matrix.det _) (a ^ 4)] using hdet

/-- The determinant of the eight-dimensional left action is the fourth
power of the native reduced norm, including on the null cone. -/
theorem det_leftRegular_eq_norm_pow_four
    (b : Module.Basis (Fin 8) ℝ (ZornMatrix ℝ)) (Z : ZornMatrix ℝ) :
    Matrix.det (LinearMap.toMatrix b b (leftRegularRepresentation Z)) =
      zornNormFun Z ^ 4 := by
  rw [LinearMap.det_toMatrix_eq_det_toMatrix b
    ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
    (leftRegularRepresentation Z), leftRegular_cartesian_matrix]
  change Matrix.det (cartesianMatrix Z) = _
  rw [← Matrix.det_submatrix_equiv_self
    (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8), cartesianMatrix_blocks]
  exact det_scalar_blocks Z.a Z.b (ZornMatrix.dot Z.x Z.y)
    (upperBlock Z) (lowerBlock Z) (lower_mul_upper Z)

end InfoGeometry.Lie.CanonicalZornRegularExactDet
