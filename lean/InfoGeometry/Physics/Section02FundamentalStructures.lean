import Mathlib.Tactic
import InfoGeometry.Physics.Section00MatrixBasisFramework
import InfoGeometry.Physics.Section01MatrixBasisIntroduction

/-!
# Section 02: codebase-grounded finite fundamental structures

The source `section02.txt` asks for vector, matrix, and quaternion
representations of spacetime.  This file keeps only the finite theorem surface
already owned by the repository:

* `Section30UnifiedMatrixFramework` owns the concrete Pauli matrices and the
  determinant/Minkowski readout;
* `Section00MatrixBasisFramework` owns the source-normalized `1 / sqrt 2`
  matrix convention, coefficient-space complex structures, finite
  Hilbert-Schmidt metric, and the ordinary-quaternion sign fence;
* `Section01MatrixBasisIntroduction` owns Pauli coordinate reconstruction for
  arbitrary complex `2 × 2` matrices.

#### BUCKET 1: CLOSED FINITE THEOREMS

Pauli square/product/anticommutation identities, the vector line element in
`(-,+,+,+)` signature, normalized matrix metric equivalence `-2 det(X)`, finite
quaternion relations for the coefficient-space complex structures, finite
Hilbert-Schmidt preservation, Pauli-basis reconstruction, and the ordinary
Hamilton-quaternion sign boundary.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

The smooth hyperkähler manifold theorem, vanishing Nijenhuis tensor on a
manifold, spinor/tangent-bundle soldering, curved-spacetime equivalence,
topological isomorphism claims, and quaternionic spacetime metric require
additional formal structures.  Ordinary Hamilton `q q*` is explicitly not used
as the Minkowski interval; the closed indefinite interval is the Pauli
determinant readout or an explicitly split convention.
-/

noncomputable section

namespace InfoGeometry.Physics.Section02FundamentalStructures

open Matrix Complex

/-- Complex `2 × 2` matrices, reused from Section30 through Section00. -/
abbrev Mat2C := _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.Mat2C

/-- Real Pauli coefficient coordinates `(t,x,y,z)`. -/
abbrev PauliCoord := _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.PauliCoord

/-- First Pauli matrix. -/
abbrev sigma1 : Mat2C := _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.sigma1

/-- Second Pauli matrix. -/
abbrev sigma2 : Mat2C := _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.sigma2

/-- Third Pauli matrix. -/
abbrev sigma3 : Mat2C := _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.sigma3

/-- Matrix form of a real spacetime point. -/
abbrev pauliMatrix : PauliCoord → Mat2C :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.pauliMatrix

/-- Source-normalized matrix `X = (1 / sqrt 2) (t I + xσ₁ + yσ₂ + zσ₃)`. -/
abbrev normalizedPauliMatrix : PauliCoord → Mat2C :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.normalizedPauliMatrix

/-- Finite Hilbert-Schmidt coefficient metric. -/
abbrev hsMetric : PauliCoord → PauliCoord → ℝ :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.hsMetric

/-- Vector line element in the source's `(-,+,+,+)` convention. -/
def vectorInterval (dt dx dy dz : ℝ) : ℝ :=
  -dt ^ 2 + dx ^ 2 + dy ^ 2 + dz ^ 2

/-- The real vector line element is the Section30 complex Minkowski form. -/
theorem vectorInterval_cast_eq_minkowskiForm (dt dx dy dz : ℝ) :
    ((vectorInterval dt dx dy dz : ℝ) : ℂ) =
      _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
        dt dx dy dz := by
  simp [vectorInterval,
    _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm]

/-! ## Pauli matrix algebra -/

/-- Pauli square packet, delegated to Section00/Section30. -/
theorem pauli_square_packet :
    sigma1 * sigma1 = 1 ∧ sigma2 * sigma2 = 1 ∧ sigma3 * sigma3 = 1 :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.pauli_square_packet

/-- Pauli product packet, delegated to Section00/Section30. -/
theorem pauli_product_packet :
    sigma1 * sigma2 = Complex.I • sigma3 ∧
      sigma2 * sigma3 = Complex.I • sigma1 ∧
        sigma3 * sigma1 = Complex.I • sigma2 :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.pauli_product_packet

/-- The distinct Pauli matrices anticommute. -/
theorem pauli_anticommutation_packet :
    sigma1 * sigma2 + sigma2 * sigma1 = 0 ∧
      sigma2 * sigma3 + sigma3 * sigma2 = 0 ∧
        sigma3 * sigma1 + sigma1 * sigma3 = 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sigma1, sigma2, sigma3, InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C,
        InfoGeometryCore.sigma3C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sigma1, sigma2, sigma3, InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C,
        InfoGeometryCore.sigma3C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sigma1, sigma2, sigma3, InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C,
        InfoGeometryCore.sigma3C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

/-! ## Matrix metric equivalence -/

/-- Unnormalized determinant readout `-det =` the `(-,+,+,+)` interval. -/
theorem unnormalized_matrix_metric_equivalence (v : PauliCoord) :
    - (pauliMatrix v).det =
      _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
        v.t v.x v.y v.z :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.neg_det_pauliMatrix_eq_minkowskiForm
    v

/-- Source-normalized determinant readout `-2 det(X) =` the `(-,+,+,+)` interval. -/
theorem normalized_matrix_metric_equivalence (v : PauliCoord) :
    - (2 : ℂ) * (normalizedPauliMatrix v).det =
      _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
        v.t v.x v.y v.z :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.normalizedPauliMatrix_neg_two_det_eq_minkowskiForm
    v

/-- The normalized matrix metric equals the vector line element. -/
theorem normalized_matrix_metric_eq_vectorInterval (v : PauliCoord) :
    - (2 : ℂ) * (normalizedPauliMatrix v).det =
      ((vectorInterval v.t v.x v.y v.z : ℝ) : ℂ) := by
  rw [normalized_matrix_metric_equivalence, vectorInterval_cast_eq_minkowskiForm]

/-! ## Coefficient-space quaternion relations and Hilbert-Schmidt metric -/

/-- All finite quaternion relations for Section00's coefficient-space complex structures. -/
theorem coefficient_complex_structure_quaternion_packet (v : PauliCoord) :
    _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI v) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.negCoord v ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ v) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.negCoord v ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK v) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.negCoord v ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ v) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK v ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK v) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI v ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI v) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI_sq v
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ_sq v
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK_sq v
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI_mul_complexJ v
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ_mul_complexK v
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK_mul_complexI v

/-- The coefficient-space complex structures preserve the finite HS metric. -/
theorem coefficient_complex_structures_preserve_hsMetric (a b : PauliCoord) :
    hsMetric
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI a)
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI b) =
        hsMetric a b ∧
      hsMetric
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ a)
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ b) =
        hsMetric a b ∧
      hsMetric
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK a)
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK b) =
        hsMetric a b := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI_preserves_hsMetric a b
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ_preserves_hsMetric a b
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK_preserves_hsMetric a b

/-! ## Basis reconstruction and quaternion sign fence -/

/-- Section01 supplies reconstruction by Pauli coordinates for every complex `2 × 2` matrix. -/
theorem pauli_basis_reconstruct (M : Mat2C) :
    _root_.InfoGeometry.Physics.Section01MatrixBasisIntroduction.pauliExpand
        (_root_.InfoGeometry.Physics.Section01MatrixBasisIntroduction.coeffT M)
        (_root_.InfoGeometry.Physics.Section01MatrixBasisIntroduction.coeffX M)
        (_root_.InfoGeometry.Physics.Section01MatrixBasisIntroduction.coeffY M)
        (_root_.InfoGeometry.Physics.Section01MatrixBasisIntroduction.coeffZ M) = M :=
  _root_.InfoGeometry.Physics.Section01MatrixBasisIntroduction.pauliExpansion_reconstruct M

/-- Ordinary Hamilton quaternion norm has the wrong spatial sign for the source metric. -/
theorem ordinary_quaternion_norm_sign_boundary :
    _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.ordinaryQuaternionNormSq
        ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) = 1 ∧
      _root_.InfoGeometry.Geometry.PauliParavectorBridge.Minkowski4.q
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.toMinkowski4
          ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ))) = -1 :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.ordinaryQuaternionNorm_not_minkowski_spatial_unit

/-- Repaired finite Section02 packet. -/
theorem section02_finite_fundamental_structures_packet (a b : PauliCoord) :
    sigma1 * sigma1 = 1 ∧
      sigma1 * sigma2 + sigma2 * sigma1 = 0 ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexJ a) =
        _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexK a ∧
      hsMetric
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI a)
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI b) =
        hsMetric a b ∧
      - (2 : ℂ) * (normalizedPauliMatrix a).det =
        ((vectorInterval a.t a.x a.y a.z : ℝ) : ℂ) ∧
      _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.ordinaryQuaternionNormSq
        ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) = 1 ∧
      _root_.InfoGeometry.Geometry.PauliParavectorBridge.Minkowski4.q
        (_root_.InfoGeometry.Physics.Section00MatrixBasisFramework.toMinkowski4
          ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ))) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pauli_square_packet.1
  · exact pauli_anticommutation_packet.1
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI_mul_complexJ a
  · exact _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.complexI_preserves_hsMetric a b
  · exact normalized_matrix_metric_eq_vectorInterval a
  · exact ordinary_quaternion_norm_sign_boundary.1
  · exact ordinary_quaternion_norm_sign_boundary.2

end InfoGeometry.Physics.Section02FundamentalStructures

end noncomputable section
