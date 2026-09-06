import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.SplitOctonionEllClosedFlowCircularBasis
import InfoGeometry.Canonical.ZornCellScalarExtensionBridge
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# Native matrix export for the finite split `G₂` derivation basis

The matrix representation here is tied to the repository-owned `CZ` basis
`diagCircularBasis`.  It is an export/readout layer only; no independent
matrix Lie algebra or bracket table is introduced.
-/

open scoped Matrix.Norms.Frobenius

namespace InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport

open InfoGeometry.Canonical
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornCellScalarExtensionBridge

noncomputable abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der
noncomputable abbrev CZEnd := Module.End ℝ CanonicalZornDerivation.CZ

noncomputable abbrev RealCell := InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℝ

/-! The same parameter action over `ℚ`, used only as the finite source for
the literal coefficient export below.  Its coordinate order is the native
`ZornVectorMatrix` order `(a, v 0, v 1, v 2, b, w 0, w 1, w 2)`. -/
abbrev RationalVZ := InfoGeometry.Algebra.ZornVectorMatrix ℚ

def rationalParameterAction (p : Fin 14 → ℚ) (X : RationalVZ) : RationalVZ :=
  ⟨p 0 * X.v 0 + p 3 * X.v 1 + p 8 * X.v 2 - p 10 * X.w 0 +
      p 9 * X.w 1 - p 4 * X.w 2,
    fun i => if i = 0 then
      p 10 * X.a - p 10 * X.b + (p 6 + p 13) * X.v 0 - p 5 * X.v 1 -
        p 11 * X.v 2 + p 8 * X.w 1 - p 3 * X.w 2
    else if i = 1 then
      -p 9 * X.a + p 9 * X.b - p 1 * X.v 0 - p 6 * X.v 1 -
        p 12 * X.v 2 - p 8 * X.w 0 + p 0 * X.w 2
    else
      p 4 * X.a - p 4 * X.b - p 2 * X.v 0 - p 7 * X.v 1 -
        p 13 * X.v 2 + p 3 * X.w 0 - p 0 * X.w 1,
    fun i => if i = 0 then
      -p 0 * X.a + p 0 * X.b - p 4 * X.v 1 - p 9 * X.v 2 -
        (p 6 + p 13) * X.w 0 + p 1 * X.w 1 + p 2 * X.w 2
    else if i = 1 then
      -p 3 * X.a + p 3 * X.b + p 4 * X.v 0 - p 10 * X.v 2 +
        p 5 * X.w 0 + p 6 * X.w 1 + p 7 * X.w 2
    else
      -p 8 * X.a + p 8 * X.b + p 9 * X.v 0 + p 10 * X.v 1 +
        p 11 * X.w 0 + p 12 * X.w 1 + p 13 * X.w 2,
    -(p 0 * X.v 0 + p 3 * X.v 1 + p 8 * X.v 2 - p 10 * X.w 0 +
      p 9 * X.w 1 - p 4 * X.w 2)⟩

def rationalAxis (i : Fin 3) : Fin 3 → ℚ := fun j => if i = j then 1 else 0

def rationalFrameVector (a b : ℚ) (v w : Fin 3 → ℚ) : RationalVZ :=
  ⟨a, v, w, b⟩

def zeroVec3 : Fin 3 → ℚ := fun _ => 0
def zeroVZ : RationalVZ := ⟨0, zeroVec3, zeroVec3, 0⟩

def rationalCircularFrame : Fin 8 → RationalVZ
  | 0 => rationalFrameVector (1 / 2 : ℚ) (1 / 2 : ℚ) zeroVec3 zeroVec3
  | 1 => rationalFrameVector 0 0 ((1 / 2 : ℚ) • rationalAxis 0) ((1 / 2 : ℚ) • rationalAxis 0)
  | 2 => rationalFrameVector 0 0 ((1 / 2 : ℚ) • rationalAxis 1) ((1 / 2 : ℚ) • rationalAxis 1)
  | 3 => rationalFrameVector 0 0 ((1 / 2 : ℚ) • rationalAxis 2) ((1 / 2 : ℚ) • rationalAxis 2)
  | 4 => rationalFrameVector (1 / 2 : ℚ) (-1 / 2 : ℚ) zeroVec3 zeroVec3
  | 5 => rationalFrameVector 0 0 (-(1 / 2 : ℚ) • rationalAxis 0) ((1 / 2 : ℚ) • rationalAxis 0)
  | 6 => rationalFrameVector 0 0 (-(1 / 2 : ℚ) • rationalAxis 1) ((1 / 2 : ℚ) • rationalAxis 1)
  | 7 => rationalFrameVector 0 0 (-(1 / 2 : ℚ) • rationalAxis 2) ((1 / 2 : ℚ) • rationalAxis 2)
  | _ => zeroVZ

def rationalCoordinates (X : RationalVZ) : Fin 8 → ℚ
  | 0 => X.a
  | 1 => X.v 0
  | 2 => X.v 1
  | 3 => X.v 2
  | 4 => X.b
  | 5 => X.w 0
  | 6 => X.w 1
  | 7 => X.w 2
  | _ => 0

def rationalCircularFrameMatrix : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => rationalCoordinates (rationalCircularFrame j) i

def rationalStandardVector (j : Fin 8) : RationalVZ :=
  match j with
  | 0 => rationalFrameVector 1 0 zeroVec3 zeroVec3
  | 1 => rationalFrameVector 0 0 (rationalAxis 0) zeroVec3
  | 2 => rationalFrameVector 0 0 (rationalAxis 1) zeroVec3
  | 3 => rationalFrameVector 0 0 (rationalAxis 2) zeroVec3
  | 4 => rationalFrameVector 0 1 zeroVec3 zeroVec3
  | 5 => rationalFrameVector 0 0 zeroVec3 (rationalAxis 0)
  | 6 => rationalFrameVector 0 0 zeroVec3 (rationalAxis 1)
  | 7 => rationalFrameVector 0 0 zeroVec3 (rationalAxis 2)
  | _ => zeroVZ

def rationalParameterMatrix (k : Fin 14) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => rationalCoordinates
    (rationalParameterAction (fun m => if k = m then 1 else 0) (rationalStandardVector j)) i

noncomputable def rationalCircularOperatorMatrix (k : Fin 14) : Matrix (Fin 8) (Fin 8) ℚ :=
  (rationalCircularFrameMatrix)⁻¹ * rationalParameterMatrix k *
    rationalCircularFrameMatrix

def explicitInverseMatrix : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 0, 0, 0, 1, 0, 0, 0;
          0, 1, 0, 0, 0, 1, 0, 0;
          0, 0, 1, 0, 0, 0, 1, 0;
          0, 0, 0, 1, 0, 0, 0, 1;
          1, 0, 0, 0, -1, 0, 0, 0;
          0, -1, 0, 0, 0, 1, 0, 0;
          0, 0, -1, 0, 0, 0, 1, 0;
          0, 0, 0, -1, 0, 0, 0, 1]

theorem rationalCircularFrameMatrix_inv :
    (rationalCircularFrameMatrix)⁻¹ = explicitInverseMatrix := by
  have hframe : rationalCircularFrameMatrix =
      !![(1/2 : ℚ), 0, 0, 0, (1/2 : ℚ), 0, 0, 0;
          0, (1/2 : ℚ), 0, 0, 0, (-1/2 : ℚ), 0, 0;
          0, 0, (1/2 : ℚ), 0, 0, 0, (-1/2 : ℚ), 0;
          0, 0, 0, (1/2 : ℚ), 0, 0, 0, (-1/2 : ℚ);
          (1/2 : ℚ), 0, 0, 0, (-1/2 : ℚ), 0, 0, 0;
          0, (1/2 : ℚ), 0, 0, 0, (1/2 : ℚ), 0, 0;
          0, 0, (1/2 : ℚ), 0, 0, 0, (1/2 : ℚ), 0;
          0, 0, 0, (1/2 : ℚ), 0, 0, 0, (1/2 : ℚ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rationalCircularFrameMatrix, rationalCircularFrame,
        rationalFrameVector, rationalAxis, rationalCoordinates, zeroVec3, zeroVZ] <;>
      simp
  rw [hframe]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [explicitInverseMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-! Rational finite table owner.  Its entries are definitionally obtained from
the explicit rational parameter action and frame conjugation. -/
def rootDerivationRationalTable : Fin 14 → Matrix (Fin 8) (Fin 8) ℚ :=
  ![
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, 1/2; 0, 0, -1/2, 0, 0, 0, -1/2, 0; 0, 1, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, -1/2; 0, 0, 1/2, 0, 0, 0, 1/2, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1/2, 0, 0, 0, 1/2, 0; 0, -1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1/2, 0, 0, 0, 1/2, 0; 0, 1/2, 0, 0, 0, -1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, 1/2; 0, 0, 0, 0, 0, 0, 0, 0; 0, -1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, 1/2; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1/2, 0, 0, 0, -1/2, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, -1/2; 0, 0, 0, 0, -1, 0, 0, 0; 0, 1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 1, 0, 0, 0, -1, 0; 0, 0, 0, 1/2, 0, 0, 0, 1/2; 0, 0, 0, 0, -1, 0, 0, 0; 0, -1/2, 0, 0, 0, -1/2, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1/2, 0, 0, 0, 1/2, 0; 0, 1/2, 0, 0, 0, -1/2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, -1; 0, 0, -1/2, 0, 0, 0, 1/2, 0; 0, 1/2, 0, 0, 0, -1/2, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1/2, 0, 0, 0, 1/2, 0; 0, 1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1/2, 0, 0, 0, -1/2, 0; 0, 1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, 1/2; 0, 0, -1/2, 0, 0, 0, 1/2, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, 1/2; 0, 0, 1/2, 0, 0, 0, -1/2, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1/2, 0, 0, 0, 1/2, 0; 0, -1/2, 0, 0, 0, -1/2, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -1; 0, 0, -1/2, 0, 0, 0, -1/2, 0; 0, 1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, 1/2; 0, 0, 0, 0, -1, 0, 0, 0; 0, 1/2, 0, 0, 0, -1/2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 0; 0, 0, 0, -1/2, 0, 0, 0, 1/2; 0, 0, 0, 0, 1, 0, 0, 0; 0, 1/2, 0, 0, 0, -1/2, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, 1/2; 0, 0, 1/2, 0, 0, 0, -1/2, 0; 0, -1, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, 1/2; 0, 0, 1/2, 0, 0, 0, -1/2, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, 1/2; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1/2, 0, 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, -1/2; 0, 0, 0, 0, 0, 0, 0, 0; 0, 1/2, 0, 0, 0, 1/2, 0, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1/2, 0, 0, 0, 1/2; 0, 0, 1/2, 0, 0, 0, 1/2, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1/2, 0, 0, 0, -1/2; 0, 0, 1/2, 0, 0, 0, 1/2, 0]),
    (!![0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0])
  ]

set_option maxHeartbeats 10000000 in
theorem rootDerivationRationalTable_matrix (k : Fin 14) :
    rootDerivationRationalTable k = rationalCircularOperatorMatrix k := by
  fin_cases k <;>
    rw [rationalCircularOperatorMatrix, rationalCircularFrameMatrix_inv] <;>
    native_decide

theorem rootDerivationRationalTable_entry (k : Fin 14) (i j : Fin 8) :
    rootDerivationRationalTable k i j = rationalCircularOperatorMatrix k i j := by
  rw [rationalCircularOperatorMatrix, rationalCircularFrameMatrix_inv]
  have h := rootDerivationRationalTable_matrix k
  rw [rationalCircularOperatorMatrix, rationalCircularFrameMatrix_inv] at h
  exact congrFun (congrFun h i) j

noncomputable section

noncomputable def nativeParameterMatrix (i : Fin 14) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix diagCircularBasis diagCircularBasis
    (rootDerivationBasis i : Der).1

noncomputable def nativeDerivationMatrix (D : Der) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix diagCircularBasis diagCircularBasis D.1

noncomputable def nativeMatrixExponential (i : Fin 14) (t : ℝ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  NormedSpace.exp (t • nativeParameterMatrix i)

@[simp] theorem nativeMatrixExponential_zero (i : Fin 14) :
    nativeMatrixExponential i 0 = 1 := by
  simp [nativeMatrixExponential]

theorem nativeMatrixExponential_add (i : Fin 14) (s t : ℝ) :
    nativeMatrixExponential i (s + t) =
      nativeMatrixExponential i s * nativeMatrixExponential i t := by
  unfold nativeMatrixExponential
  rw [add_smul]
  apply NormedSpace.exp_add_of_commute
  exact (Commute.refl (nativeParameterMatrix i)).smul_left s |>.smul_right t

theorem hasDerivAt_nativeMatrixExponential (i : Fin 14) (t : ℝ) :
    HasDerivAt (nativeMatrixExponential i)
      (nativeMatrixExponential i t * nativeParameterMatrix i) t := by
  simpa [nativeMatrixExponential] using
    (hasDerivAt_exp_smul_const (x := nativeParameterMatrix i) (t := t))

theorem nativeDerivationMatrix_map_lie (D E : Der) :
    nativeDerivationMatrix ⁅D, E⁆ =
      nativeDerivationMatrix D * nativeDerivationMatrix E -
        nativeDerivationMatrix E * nativeDerivationMatrix D := by
  change LinearMap.toMatrix diagCircularBasis diagCircularBasis ⁅D, E⁆.1 = _
  change LinearMap.toMatrixAlgEquiv diagCircularBasis
      (D.1 * E.1 - E.1 * D.1) = _
  simp only [map_sub, LinearMap.toMatrixAlgEquiv_mul]
  rfl

theorem rootDerivationMatrix_map_lie (i j : Fin 14) :
    nativeDerivationMatrix ⁅rootDerivationBasis i, rootDerivationBasis j⁆ =
      nativeParameterMatrix i * nativeParameterMatrix j -
        nativeParameterMatrix j * nativeParameterMatrix i := by
  simpa [nativeDerivationMatrix, nativeParameterMatrix] using
    (nativeDerivationMatrix_map_lie
      (rootDerivationBasis i : Der) (rootDerivationBasis j : Der))

theorem rootDerivationMatrix_map_lie_entry (i j : Fin 14) (r c : Fin 8) :
    nativeDerivationMatrix ⁅rootDerivationBasis i, rootDerivationBasis j⁆ r c =
      ∑ m : Fin 8, nativeParameterMatrix i r m * nativeParameterMatrix j m c -
        ∑ m : Fin 8, nativeParameterMatrix j r m * nativeParameterMatrix i m c := by
  have h := rootDerivationMatrix_map_lie i j
  exact congrFun (congrFun h r) c

def rootBracketCoefficient (i j k : Fin 14) : ℝ :=
  (canonicalParameterLinearEquiv.symm
    ⁅rootDerivation i, rootDerivation j⁆) k

theorem rootBracketCoefficient_swap (i j k : Fin 14) :
    rootBracketCoefficient j i k = -rootBracketCoefficient i j k := by
  change (canonicalParameterLinearEquiv.symm ⁅rootDerivation j, rootDerivation i⁆) k =
    -(canonicalParameterLinearEquiv.symm ⁅rootDerivation i, rootDerivation j⁆) k
  have h : ⁅rootDerivation j, rootDerivation i⁆ =
      -⁅rootDerivation i, rootDerivation j⁆ := by
    simpa only [neg_neg] using
      congrArg Neg.neg (lie_skew (rootDerivation i) (rootDerivation j))
  rw [h]
  exact congrFun
    (canonicalParameterLinearEquiv.symm.map_neg
      ⁅rootDerivation i, rootDerivation j⁆) k

@[simp] theorem rootBracketCoefficient_self (i k : Fin 14) :
    rootBracketCoefficient i i k = 0 := by
  simp [rootBracketCoefficient]

theorem rootBracketCoefficient_eq_basis_repr (i j k : Fin 14) :
    rootBracketCoefficient i j k =
      (rootDerivationBasis.repr ⁅rootDerivation i, rootDerivation j⁆) k := by
  simp [rootBracketCoefficient, rootDerivationBasis, rootDerivation]

theorem rootBracket_eq_sum_rootDerivation (i j : Fin 14) :
    ⁅rootDerivation i, rootDerivation j⁆ =
      ∑ k : Fin 14, rootBracketCoefficient i j k • rootDerivation k := by
  rw [← rootDerivationBasis.sum_repr ⁅rootDerivation i, rootDerivation j⁆]
  congr 1
  funext k
  simp [rootBracketCoefficient, rootDerivationBasis, rootDerivation]
  have hpk : Pi.single k (1 : ℝ) = parameterUnit k := by
    ext l
    by_cases h : l = k <;>
      simp [parameterUnit, Pi.single_apply, h]
  rw [hpk]

abbrev structureConstant (i j k : Fin 14) : ℝ :=
  rootBracketCoefficient i j k

theorem bracket_eq_sum_structure_constants (i j : Fin 14) :
    ⁅rootDerivation i, rootDerivation j⁆ =
      ∑ k : Fin 14, structureConstant i j k • rootDerivation k := by
  exact rootBracket_eq_sum_rootDerivation i j

/-! The native circular basis pulled back to the explicit cell carrier. -/
noncomputable def transportedCellBasis : Module.Basis (Fin 8) ℝ RealCell :=
  diagCircularBasis.map realCellToCZ.symm

@[simp] theorem realCellToCZ_transportedCellBasis (i : Fin 8) :
    realCellToCZ (transportedCellBasis i) = diagCircularBasis i := by
  simp [transportedCellBasis]

noncomputable def transportedRootDerivation (i : Fin 14) : Module.End ℝ RealCell :=
  realCellToCZ.symm.toLinearMap.comp
    ((rootDerivationBasis i : Der).1.comp realCellToCZ.toLinearMap)

theorem realCellToCZ_transportedRootDerivation
    (i : Fin 14) (x : RealCell) :
    realCellToCZ (transportedRootDerivation i x) =
      (rootDerivationBasis i : Der).1 (realCellToCZ x) := by
  simp [transportedRootDerivation]

noncomputable def transportedRootDerivationMatrix (i : Fin 14) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix transportedCellBasis transportedCellBasis
    (transportedRootDerivation i)

theorem transportedRootDerivationMatrix_entry
    (i : Fin 14) (r c : Fin 8) :
    transportedRootDerivationMatrix i r c = nativeParameterMatrix i r c := by
  simp [transportedRootDerivationMatrix, transportedRootDerivation,
    nativeParameterMatrix, transportedCellBasis, LinearMap.toMatrix_apply,
    Module.Basis.map_repr]

theorem transportedRootDerivationMatrix_eq_nativeParameterMatrix
    (i : Fin 14) :
    transportedRootDerivationMatrix i = nativeParameterMatrix i := by
  ext r c
  exact transportedRootDerivationMatrix_entry i r c

/-- Canonical name for the matrix representation consumed by external
certificates.  It is deliberately an alias of the native-basis readout. -/
abbrev rootDerivationMatrix := nativeParameterMatrix

theorem transportedRootDerivationMatrix_eq_rootDerivationMatrix
    (i : Fin 14) :
    transportedRootDerivationMatrix i = rootDerivationMatrix i := by
  exact transportedRootDerivationMatrix_eq_nativeParameterMatrix i

theorem rootDerivationMatrix_repr (i : Fin 14) :
    rootDerivationMatrix i =
      LinearMap.toMatrix diagCircularBasis diagCircularBasis
        (rootDerivationBasis i : Der).1 :=
  rfl

theorem nativeParameterMatrix_apply (i : Fin 14) (j k : Fin 8) :
    nativeParameterMatrix i j k =
      (diagCircularBasis.repr
        ((rootDerivationBasis i : Der).1 (diagCircularBasis k))) j := by
  simp [nativeParameterMatrix, LinearMap.toMatrix_apply]

@[simp] theorem rootDerivationMatrix_entry (i : Fin 14) (r c : Fin 8) :
    rootDerivationMatrix i r c =
      (diagCircularBasis.repr
        ((rootDerivationBasis i : Der).1 (diagCircularBasis c))) r := by
  exact nativeParameterMatrix_apply i r c

theorem rootDerivationMatrix_mulVec_repr (i : Fin 14)
    (X : CanonicalZornDerivation.CZ) :
    Matrix.mulVec (rootDerivationMatrix i) (diagCircularBasis.repr X) =
      diagCircularBasis.repr ((rootDerivationBasis i : Der).1 X) := by
  exact LinearMap.toMatrix_mulVec_repr
    diagCircularBasis diagCircularBasis (rootDerivationBasis i : Der).1 X

theorem nativeParameterMatrix_is_derivation (i : Fin 14) :
    IsDerivation ((rootDerivationBasis i : Der).1) := by
  exact (rootDerivationBasis i : Der).property

theorem nativeParameterMatrix_injective :
    Function.Injective nativeParameterMatrix := by
  intro i j hij
  have hmaps :
      (rootDerivationBasis i : Der).1 =
        (rootDerivationBasis j : Der).1 := by
    apply (LinearMap.toMatrix diagCircularBasis diagCircularBasis).injective
    simpa [nativeParameterMatrix] using hij
  apply rootDerivationBasis.injective
  exact Subtype.ext hmaps

theorem nativeParameterMatrix_eq_zero_iff (i : Fin 14) :
    nativeParameterMatrix i = 0 ↔
      (rootDerivationBasis i : Der).1 = 0 := by
  constructor
  · intro h
    apply (LinearMap.toMatrix diagCircularBasis diagCircularBasis).injective
    simpa [nativeParameterMatrix] using h
  · intro h
    simp [nativeParameterMatrix, h]

end

end InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport

