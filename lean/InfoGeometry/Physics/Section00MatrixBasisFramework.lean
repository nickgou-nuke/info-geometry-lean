import Mathlib.Tactic
import InfoGeometry.Canonical.BiQuaternionKahlerFinite
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Optics.JonesPoincareSphere
import InfoGeometry.Section16
import InfoGeometry.Physics.Section30UnifiedMatrixFramework
import InfoGeometry.Twistor.PenroseTwistor

/-!
# Section 00: codebase-grounded finite matrix-basis framework

This module is the Section00 front door over existing finite owners:

* `Canonical.BiQuaternionKahlerFinite` owns the concrete `R^4` quaternionic
  complex structures;
* `Physics.Section30UnifiedMatrixFramework` owns the Pauli matrices and the
  finite determinant/Minkowski readout;
* `Geometry.PauliParavectorBridge` owns the geometry-facing paravector
  determinant theorem.

Section00 adds only the coefficient-structure API needed by the introductory
text and re-exports the matrix-basis facts through those owners.

#### BUCKET 1: CLOSED FINITE THEOREMS

Owner alignment with `BiQuaternionKahlerFinite.I4c/J4c/K4c`, quaternion
relations on coefficient space, Hilbert-Schmidt metric preservation, Section30
Pauli square/product identities, normalized and unnormalized
Section30/geometry determinant readouts, and the ordinary-quaternion norm sign
boundary.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Full hyperkähler manifolds, spinor-bundle/tangent-bundle soldering,
continuum curvature, quantum-gravity emergence, and physical interpretation
of the matrix basis remain outside this finite file. The source's quaternion
metric sentence is not taken as an ordinary Hamilton-quaternion norm theorem:
ordinary `q q*` is Euclidean-positive, while the Minkowski readout belongs to
the Pauli determinant or an explicitly indefinite split-quaternion convention.
-/

noncomputable section

namespace InfoGeometry.Physics.Section00MatrixBasisFramework

open Matrix Complex

/-- Complex `2 × 2` matrices, delegated to the Section30 Pauli owner. -/
abbrev Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.Mat2C

/-- First Pauli matrix, delegated to the Section30 Pauli owner. -/
abbrev sigma1 : Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma1

/-- Second Pauli matrix, delegated to the Section30 Pauli owner. -/
abbrev sigma2 : Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma2

/-- Third Pauli matrix, delegated to the Section30 Pauli owner. -/
abbrev sigma3 : Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma3

/-- Real coordinates in the Pauli basis `{σ₀,σ₁,σ₂,σ₃}`. -/
structure PauliCoord where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

@[ext]
theorem PauliCoord.ext {a b : PauliCoord}
    (ht : a.t = b.t) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  cases a
  cases b
  simp at ht hx hy hz
  simp [ht, hx, hy, hz]

/-- Coordinate negation. -/
def negCoord (v : PauliCoord) : PauliCoord :=
  { t := -v.t, x := -v.x, y := -v.y, z := -v.z }

/-- Section00 complex structure `I` on Pauli coefficient space. -/
def complexI (v : PauliCoord) : PauliCoord :=
  { t := -v.x, x := v.t, y := -v.z, z := v.y }

/-- Section00 complex structure `J` on Pauli coefficient space. -/
def complexJ (v : PauliCoord) : PauliCoord :=
  { t := -v.y, x := v.z, y := v.t, z := -v.x }

/-- Section00 complex structure `K` on Pauli coefficient space. -/
def complexK (v : PauliCoord) : PauliCoord :=
  { t := -v.z, x := -v.y, y := v.x, z := v.t }

/-- Hilbert-Schmidt metric in the Pauli basis: `1/2 Tr(σᵢ σⱼ)=δᵢⱼ`. -/
def hsMetric (a b : PauliCoord) : ℝ :=
  a.t * b.t + a.x * b.x + a.y * b.y + a.z * b.z

/-- Convert Section00 coordinates to the canonical finite `R^4` owner. -/
def toR4 (v : PauliCoord) :
    _root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.R4 :=
  ![v.t, v.x, v.y, v.z]

/-- Convert a canonical finite `R^4` vector back to Section00 coordinates. -/
def ofR4 (v : _root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.R4) : PauliCoord :=
  { t := v 0, x := v 1, y := v 2, z := v 3 }

/-- Section00 `I` is exactly the canonical finite owner `I4c`. -/
theorem complexI_eq_owner_I4c (v : PauliCoord) :
    complexI v =
      ofR4 (_root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.I4c.mulVec (toR4 v)) := by
  ext <;> simp [complexI, ofR4, toR4,
    _root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.I4c, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

/-- Section00 `J` is exactly the canonical finite owner `J4c`. -/
theorem complexJ_eq_owner_J4c (v : PauliCoord) :
    complexJ v =
      ofR4 (_root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c.mulVec (toR4 v)) := by
  ext <;> simp [complexJ, ofR4, toR4,
    _root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

/-- Section00 `K` is exactly the canonical finite owner `K4c`. -/
theorem complexK_eq_owner_K4c (v : PauliCoord) :
    complexK v =
      ofR4 (_root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.K4c.mulVec (toR4 v)) := by
  ext <;> simp [complexK, ofR4, toR4,
    _root_.InfoGeometry.Canonical.BiQuaternionKahlerFinite.K4c, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

/-- `I² = -Id`. -/
theorem complexI_sq (v : PauliCoord) :
    complexI (complexI v) = negCoord v := by
  ext <;> simp [complexI, negCoord]

/-- `J² = -Id`. -/
theorem complexJ_sq (v : PauliCoord) :
    complexJ (complexJ v) = negCoord v := by
  ext <;> simp [complexJ, negCoord]

/-- `K² = -Id`. -/
theorem complexK_sq (v : PauliCoord) :
    complexK (complexK v) = negCoord v := by
  ext <;> simp [complexK, negCoord]

/-- `IJ = K`. -/
theorem complexI_mul_complexJ (v : PauliCoord) :
    complexI (complexJ v) = complexK v := by
  ext <;> simp [complexI, complexJ, complexK]

/-- `JK = I`. -/
theorem complexJ_mul_complexK (v : PauliCoord) :
    complexJ (complexK v) = complexI v := by
  ext <;> simp [complexI, complexJ, complexK]

/-- `KI = J`. -/
theorem complexK_mul_complexI (v : PauliCoord) :
    complexK (complexI v) = complexJ v := by
  ext <;> simp [complexI, complexJ, complexK]

/-- `JI = -K`. -/
theorem complexJ_mul_complexI (v : PauliCoord) :
    complexJ (complexI v) = negCoord (complexK v) := by
  ext <;> simp [complexI, complexJ, complexK, negCoord]

/-- `KJ = -I`. -/
theorem complexK_mul_complexJ (v : PauliCoord) :
    complexK (complexJ v) = negCoord (complexI v) := by
  ext <;> simp [complexI, complexJ, complexK, negCoord]

/-- `IK = -J`. -/
theorem complexI_mul_complexK (v : PauliCoord) :
    complexI (complexK v) = negCoord (complexJ v) := by
  ext <;> simp [complexI, complexJ, complexK, negCoord]

/-- `I` preserves the finite Hilbert-Schmidt metric. -/
theorem complexI_preserves_hsMetric (a b : PauliCoord) :
    hsMetric (complexI a) (complexI b) = hsMetric a b := by
  simp [hsMetric, complexI]
  ring

/-- `J` preserves the finite Hilbert-Schmidt metric. -/
theorem complexJ_preserves_hsMetric (a b : PauliCoord) :
    hsMetric (complexJ a) (complexJ b) = hsMetric a b := by
  simp [hsMetric, complexJ]
  ring

/-- `K` preserves the finite Hilbert-Schmidt metric. -/
theorem complexK_preserves_hsMetric (a b : PauliCoord) :
    hsMetric (complexK a) (complexK b) = hsMetric a b := by
  simp [hsMetric, complexK]
  ring

/-! ## Pauli matrix owner readouts -/

/-- The Section00 Hermitian matrix is the Section30 spacetime matrix. -/
def pauliMatrix (v : PauliCoord) : Mat2C :=
  _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.spacetimeMatrix v.t v.x v.y v.z

/-- Geometry-facing paravector with the same coordinates. -/
def toMinkowski4 (v : PauliCoord) :
    _root_.InfoGeometry.Geometry.PauliParavectorBridge.Minkowski4 :=
  { t := v.t, x := v.x, y := v.y, z := v.z }

/-- Pauli square packet, delegated to Section30. -/
theorem pauli_square_packet :
    sigma1 * sigma1 = 1 ∧ sigma2 * sigma2 = 1 ∧ sigma3 * sigma3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma1_sq
  · exact _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma2_sq
  · exact _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma3_sq

/-- Pauli product packet, delegated to Section30. -/
theorem pauli_product_packet :
    sigma1 * sigma2 = Complex.I • sigma3 ∧
      sigma2 * sigma3 = Complex.I • sigma1 ∧
        sigma3 * sigma1 = Complex.I • sigma2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma1_mul_sigma2
  · exact _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma2_mul_sigma3
  · exact _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma3_mul_sigma1

/-- Section30 determinant readout for the Section00 Pauli matrix. -/
theorem pauliMatrix_det (v : PauliCoord) :
    (pauliMatrix v).det =
      (v.t : ℂ) ^ 2 - (v.x : ℂ) ^ 2 - (v.y : ℂ) ^ 2 - (v.z : ℂ) ^ 2 := by
  simpa [pauliMatrix] using
    _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.spacetimeMatrix_det
      v.t v.x v.y v.z

/-- Section30 determinant readout as the `(-,+,+,+)` Minkowski form. -/
theorem neg_det_pauliMatrix_eq_minkowskiForm (v : PauliCoord) :
    - (pauliMatrix v).det =
      _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
        v.t v.x v.y v.z := by
  simpa [pauliMatrix] using
    _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.neg_det_spacetimeMatrix_eq_minkowskiForm
      v.t v.x v.y v.z

/-- Source-normalized Pauli matrix `X = (1 / sqrt 2) (t I + x σ₁ + y σ₂ + z σ₃)`. -/
def normalizedPauliMatrix (v : PauliCoord) : Mat2C :=
  ((Real.sqrt 2 : ℂ)⁻¹) • pauliMatrix v

/--
The source normalization gives `-2 det(X)` as the `(-,+,+,+)` Minkowski form.

This is a finite determinant theorem, derived from Section30's unnormalized
owner identity; it is not a continuum metric or field-equation claim.
-/
theorem normalizedPauliMatrix_neg_two_det_eq_minkowskiForm (v : PauliCoord) :
    - (2 : ℂ) * (normalizedPauliMatrix v).det =
      _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
        v.t v.x v.y v.z := by
  rw [normalizedPauliMatrix, Matrix.det_smul, pauliMatrix_det]
  simp [Fintype.card_fin, _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm]
  rw [show (((↑(Real.sqrt 2) : ℂ) ^ 2)⁻¹) = (1 / 2 : ℂ) by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num]
  ring

/-- Ordinary Hamilton-quaternion norm squared on coordinates. -/
def ordinaryQuaternionNormSq (v : PauliCoord) : ℝ :=
  v.t ^ 2 + v.x ^ 2 + v.y ^ 2 + v.z ^ 2

/--
Finite sign fence: ordinary Hamilton `q q*` is not the Minkowski form.

At the spatial unit vector `(0,1,0,0)`, the ordinary quaternion norm is `+1`
while the Pauli/Minkowski determinant readout is `-1`.
-/
theorem ordinaryQuaternionNorm_not_minkowski_spatial_unit :
    ordinaryQuaternionNormSq { t := 0, x := 1, y := 0, z := 0 } = 1 ∧
      _root_.InfoGeometry.Geometry.PauliParavectorBridge.Minkowski4.q
        (toMinkowski4 { t := 0, x := 1, y := 0, z := 0 }) = -1 := by
  simp [ordinaryQuaternionNormSq, toMinkowski4,
    _root_.InfoGeometry.Geometry.PauliParavectorBridge.Minkowski4.q]

/-- Geometry-facing determinant readout through `PauliParavectorBridge`. -/
theorem geometry_pauli_det (v : PauliCoord) :
    Matrix.det
        (_root_.InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix (toMinkowski4 v)) =
      (((toMinkowski4 v).q : ℝ) : ℂ) := by
  simpa [toMinkowski4] using
    _root_.InfoGeometry.Geometry.PauliParavectorBridge.det_pauliMatrix (toMinkowski4 v)

/--
Finite Section00 packet:
coefficient-space quaternion relations, Hilbert-Schmidt compatibility, and
the owner-backed Pauli determinant readout are closed finite matrix-basis facts.
-/
theorem section00_finite_matrix_basis_packet (a b : PauliCoord) :
    complexI (complexJ a) = complexK a ∧
      complexJ (complexK a) = complexI a ∧
        complexK (complexI a) = complexJ a ∧
          hsMetric (complexI a) (complexI b) = hsMetric a b ∧
            hsMetric (complexJ a) (complexJ b) = hsMetric a b ∧
              hsMetric (complexK a) (complexK b) = hsMetric a b ∧
                - (pauliMatrix a).det =
                  _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
                    a.t a.x a.y a.z ∧
                  - (2 : ℂ) * (normalizedPauliMatrix a).det =
                    _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
                      a.t a.x a.y a.z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact complexI_mul_complexJ a
  · exact complexJ_mul_complexK a
  · exact complexK_mul_complexI a
  · exact complexI_preserves_hsMetric a b
  · exact complexJ_preserves_hsMetric a b
  · exact complexK_preserves_hsMetric a b
  · exact neg_det_pauliMatrix_eq_minkowskiForm a
  · exact normalizedPauliMatrix_neg_two_det_eq_minkowskiForm a

end InfoGeometry.Physics.Section00MatrixBasisFramework

end noncomputable section
