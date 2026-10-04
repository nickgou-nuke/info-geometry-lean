import InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CASData

/-!
# Rational alignment of the CAS and native `G₂` generator orders

The CAS witness uses `(E11,E22,U0,U1,U2,V0,V1,V2)` while the native Zorn
readout uses `(a,v0,v1,v2,b,w0,w1,w2)`.  This file records only the rational
change-of-basis witness; its source is the reproducible CAS aligner, and all
finite algebraic facts below are replayed by Lean.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2BasisAlignment

def casToNativeBasis : Matrix (Fin 14) (Fin 14) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/- Structural description of the signed-permutation witness.  The literal
   matrix above remains the serialization boundary. -/
def casColumn : Fin 14 → Fin 14
  | 0 => 10 | 1 => 5 | 2 => 11 | 3 => 9 | 4 => 8 | 5 => 1 | 6 => 6
  | 7 => 12 | 8 => 4 | 9 => 3 | 10 => 0 | 11 => 2 | 12 => 7 | 13 => 13

def casSign : Fin 14 → ℚ
  | 3 => -1 | 9 => -1 | _ => 1

def casToNativeBasisStructural : Matrix (Fin 14) (Fin 14) ℚ :=
  fun i j => if j = casColumn i then casSign i else 0

theorem casColumn_bijective : Function.Bijective casColumn := by
  decide

def casPermutation : Equiv.Perm (Fin 14) :=
  Equiv.ofBijective casColumn casColumn_bijective

def casToNativeBasisDiagonal : Matrix (Fin 14) (Fin 14) ℚ :=
  Matrix.diagonal casSign

theorem casToNativeBasisStructural_eq_diagonal_perm :
    casToNativeBasisStructural =
    casToNativeBasisDiagonal * casPermutation.permMatrix ℚ := by
  ext i j
  by_cases h : j = casColumn i
  · simp [casToNativeBasisStructural, casToNativeBasisDiagonal,
      casPermutation, Equiv.Perm.permMatrix, h]
  · simp [casToNativeBasisStructural, casToNativeBasisDiagonal,
      casPermutation, Equiv.Perm.permMatrix, h, eq_comm]

theorem casToNativeBasisStructural_det_ne_zero :
    casToNativeBasisStructural.det ≠ 0 := by
  rw [casToNativeBasisStructural_eq_diagonal_perm, Matrix.det_mul,
    Matrix.det_permutation]
  simp only [casToNativeBasisDiagonal, Matrix.det_diagonal]
  apply mul_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro i hi
    fin_cases i <;> norm_num [casSign]
  · simp

theorem casToNativeBasis_eq_structural :
    casToNativeBasis = casToNativeBasisStructural := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [casToNativeBasis, casToNativeBasisStructural, casColumn, casSign,
      eq_comm]

theorem casToNativeBasis_det_ne_zero : casToNativeBasis.det ≠ 0 := by
  rw [casToNativeBasis_eq_structural]
  exact casToNativeBasisStructural_det_ne_zero

/- The column convention is `B_CAS = B_native * P`: column `i` of `P`
   contains the coefficients of CAS generator `i` in the native basis. -/
def alignedCASBasisMatrix (i : Fin 14) : Matrix (Fin 8) (Fin 8) ℚ :=
  ∑ j : Fin 14, casToNativeBasis j i •
    (InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rationalCircularFrameMatrix *
      InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.rootDerivationRationalTable j *
      InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport.explicitInverseMatrix)

theorem casBasisMatrix_eq_aligned (i : Fin 14) :
    InfoGeometry.Lie.CanonicalZornG2CASData.casBasisMatrix i =
      alignedCASBasisMatrix i := by
  fin_cases i <;> native_decide

end InfoGeometry.Lie.CanonicalZornG2BasisAlignment
