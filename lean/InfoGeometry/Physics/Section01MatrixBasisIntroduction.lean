import Mathlib
import InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
import InfoGeometry.Physics.Section00MatrixBasisFramework
import InfoGeometry.Physics.Section30UnifiedMatrixFramework

/-!
# Section 01: codebase-grounded finite Pauli basis introduction

This module introduces the Pauli coordinate basis by leaning on the established
owners:

* `Canonical.UnifiedMatrixQuantumGeometryFinite` owns Pauli algebra, traces,
  quaternion sign correction, normalized determinant readout, and Bloch
  determinant/commutator facts;
* `Physics.Section30UnifiedMatrixFramework` owns the real-parameter Pauli
  matrix, Bloch density matrices, and Bloch/Minkowski readouts;
* `Physics.Section00MatrixBasisFramework` is the Section00 front door tying the
  matrix basis to the finite `R4` coefficient structures and the source-normalized
  determinant convention.

Section01 adds the missing coordinate-basis theorem: coefficient readback is
inverse to Pauli expansion for every complex `2 × 2` matrix.

#### BUCKET 1: CLOSED FINITE THEOREMS

Owner-backed Pauli square/product/trace packets, coefficient readback,
reconstruction, coordinate injectivity, the normalized spacetime determinant
readout, Bloch trace/determinant readouts, and the Section01 finite packets.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Quantum-gravity unification, emergent spacetime, hyperkähler manifold geometry,
entanglement-as-connection, evolution-as-translation, spinor/tangent-bundle
soldering, density-matrix positivity as an ordered cone, and continuum
connection/curvature claims from the introduction remain outside this finite
matrix-basis module.
-/

noncomputable section

namespace InfoGeometry.Physics.Section01MatrixBasisIntroduction

open Matrix Complex

@[simp] theorem I_sq : (Complex.I : ℂ) ^ 2 = (-1 : ℂ) := by
  simp

/-- Complex `2 × 2` matrices, reused from the repaired Section 30 Pauli layer. -/
abbrev Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.Mat2C

/-- First Pauli matrix, reused from Section 30. -/
abbrev sigma1 : Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma1

/-- Second Pauli matrix, reused from Section 30. -/
abbrev sigma2 : Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma2

/-- Third Pauli matrix, reused from Section 30. -/
abbrev sigma3 : Mat2C := _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.sigma3

/-- Section00 real Pauli coordinate record. -/
abbrev PauliCoord :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.PauliCoord

/-- Source-normalized spacetime matrix from Section00. -/
abbrev normalizedPauliMatrix : PauliCoord → Mat2C :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.normalizedPauliMatrix

/-- Qubit Bloch density matrix from the Section30 matrix owner. -/
abbrev blochMatrix : ℝ → ℝ → ℝ → Mat2C :=
  _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.blochMatrix

/-! ## Owner-backed Pauli algebra packets -/

/-- Section01 reuses the Section00/Section30 Pauli square owner packet. -/
theorem pauli_square_packet :
    sigma1 * sigma1 = 1 ∧ sigma2 * sigma2 = 1 ∧ sigma3 * sigma3 = 1 :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.pauli_square_packet

/-- Section01 reuses the Section00/Section30 Pauli product owner packet. -/
theorem pauli_product_packet :
    sigma1 * sigma2 = Complex.I • sigma3 ∧
      sigma2 * sigma3 = Complex.I • sigma1 ∧
        sigma3 * sigma1 = Complex.I • sigma2 :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.pauli_product_packet

/--
The three non-scalar Pauli basis elements are traceless.

This is delegated to the canonical finite Pauli owner and transported through
the Section30 definitions.
-/
theorem pauli_trace_packet :
    sigma1.trace = 0 ∧ sigma2.trace = 0 ∧ sigma3.trace = 0 := by
  constructor
  · simp [sigma1, InfoGeometryCore.sigma1C, Matrix.trace, Fin.sum_univ_two]
  · constructor
    · simp [sigma2, InfoGeometryCore.sigma2C, Matrix.trace, Fin.sum_univ_two]
    · simp [sigma3, InfoGeometryCore.sigma3C, Matrix.trace, Fin.sum_univ_two]

/-! ## Owner-backed spacetime and qubit-density readouts -/

/--
The normalized spacetime matrix used by Section00 reads back the Minkowski
quadratic form by determinant with the source convention `-2 det`.
-/
theorem normalized_spacetime_det_readout (v : PauliCoord) :
    - (2 : ℂ) * (normalizedPauliMatrix v).det =
      _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
        v.t v.x v.y v.z :=
  _root_.InfoGeometry.Physics.Section00MatrixBasisFramework.normalizedPauliMatrix_neg_two_det_eq_minkowskiForm
    v

/-- Bloch qubit matrices have unit trace in the finite Section30 owner. -/
theorem bloch_density_trace (nx ny nz : ℝ) :
    (blochMatrix nx ny nz).trace = 1 :=
  _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.blochMatrix_trace
    nx ny nz

/-- The finite Bloch determinant readout. -/
theorem bloch_density_det (nx ny nz : ℝ) :
    (blochMatrix nx ny nz).det =
      ((1 : ℂ) - (nx : ℂ)^2 - (ny : ℂ)^2 - (nz : ℂ)^2) / 4 :=
  _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.blochMatrix_det
    nx ny nz

/-- A unit Bloch vector gives a rank-one boundary point, expressed by determinant zero. -/
theorem bloch_density_det_zero_of_unit_norm {nx ny nz : ℝ}
    (h : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    (blochMatrix nx ny nz).det = 0 :=
  _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.blochMatrix_det_eq_zero_of_unit_norm
    h

/-- Complex Pauli expansion `a I + b σ₁ + c σ₂ + d σ₃`. -/
def pauliExpand (a b c d : ℂ) : Mat2C :=
  a • (1 : Mat2C) + b • sigma1 + c • sigma2 + d • sigma3

/-- Scalar/identity coefficient readback. -/
def coeffT (M : Mat2C) : ℂ :=
  (M 0 0 + M 1 1) / 2

/-- First Pauli coefficient readback. -/
def coeffX (M : Mat2C) : ℂ :=
  (M 0 1 + M 1 0) / 2

/-- Second Pauli coefficient readback. -/
def coeffY (M : Mat2C) : ℂ :=
  (Complex.I / 2) * (M 0 1 - M 1 0)

/-- Third Pauli coefficient readback. -/
def coeffZ (M : Mat2C) : ℂ :=
  (M 0 0 - M 1 1) / 2

/-- The scalar/identity readback recovers the scalar coefficient. -/
theorem coeffT_pauliExpand (a b c d : ℂ) :
    coeffT (pauliExpand a b c d) = a := by
  simp [coeffT, pauliExpand, sigma1, sigma2, sigma3,
    InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C, InfoGeometryCore.sigma3C]
  field_simp
  try ring

/-- The first Pauli readback recovers the `σ₁` coefficient. -/
theorem coeffX_pauliExpand (a b c d : ℂ) :
    coeffX (pauliExpand a b c d) = b := by
  simp [coeffX, pauliExpand, sigma1, sigma2, sigma3,
    InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C, InfoGeometryCore.sigma3C]
  field_simp
  try ring

/-- The second Pauli readback recovers the `σ₂` coefficient. -/
theorem coeffY_pauliExpand (a b c d : ℂ) :
    coeffY (pauliExpand a b c d) = c := by
  simp [coeffY, pauliExpand, sigma1, sigma2, sigma3,
    InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C, InfoGeometryCore.sigma3C]
  field_simp
  try rw [I_sq]
  try ring

/-- The third Pauli readback recovers the `σ₃` coefficient. -/
theorem coeffZ_pauliExpand (a b c d : ℂ) :
    coeffZ (pauliExpand a b c d) = d := by
  simp [coeffZ, pauliExpand, sigma1, sigma2, sigma3,
    InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C, InfoGeometryCore.sigma3C]

/-- Every complex `2 × 2` matrix is reconstructed by its Pauli coefficients. -/
theorem pauliExpansion_reconstruct (M : Mat2C) :
    pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliExpand, coeffT, coeffX, coeffY, coeffZ,
      coeffT_pauliExpand, coeffX_pauliExpand, coeffY_pauliExpand, coeffZ_pauliExpand,
      sigma1, sigma2, sigma3,
      InfoGeometryCore.sigma1C, InfoGeometryCore.sigma2C, InfoGeometryCore.sigma3C, I_sq]
  all_goals try ring_nf
  all_goals try rw [I_sq]
  all_goals try ring

/-- The Pauli expansion has unique coefficients. -/
theorem pauliExpand_injective_coords {a b c d a' b' c' d' : ℂ}
    (h : pauliExpand a b c d = pauliExpand a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have ht : coeffT (pauliExpand a b c d) = coeffT (pauliExpand a' b' c' d') := by
    rw [h]
  have hx : coeffX (pauliExpand a b c d) = coeffX (pauliExpand a' b' c' d') := by
    rw [h]
  have hy : coeffY (pauliExpand a b c d) = coeffY (pauliExpand a' b' c' d') := by
    rw [h]
  have hz : coeffZ (pauliExpand a b c d) = coeffZ (pauliExpand a' b' c' d') := by
    rw [h]
  simpa [coeffT_pauliExpand, coeffX_pauliExpand, coeffY_pauliExpand,
    coeffZ_pauliExpand] using And.intro ht (And.intro hx (And.intro hy hz))

/-- Repaired finite Section01 packet: existence and uniqueness of Pauli coordinates. -/
theorem section01_finite_basis_packet (M : Mat2C) :
    sigma1 * sigma1 = 1 ∧
      sigma2 * sigma2 = 1 ∧
        sigma3 * sigma3 = 1 ∧
          sigma1.trace = 0 ∧
            sigma2.trace = 0 ∧
              sigma3.trace = 0 ∧
                pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M) = M ∧
      coeffT (pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M)) = coeffT M ∧
        coeffX (pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M)) = coeffX M ∧
          coeffY (pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M)) = coeffY M ∧
            coeffZ (pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M)) = coeffZ M := by
  exact ⟨pauli_square_packet.1,
    pauli_square_packet.2.1,
    pauli_square_packet.2.2,
    pauli_trace_packet.1,
    pauli_trace_packet.2.1,
    pauli_trace_packet.2.2,
    pauliExpansion_reconstruct M,
    coeffT_pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M),
    coeffX_pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M),
    coeffY_pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M),
    coeffZ_pauliExpand (coeffT M) (coeffX M) (coeffY M) (coeffZ M)⟩

/--
Repaired finite Section01 introduction packet: the same Pauli basis supports the
closed spacetime determinant and qubit Bloch trace/determinant statements.
-/
theorem section01_intro_matrix_quantum_packet
    (v : PauliCoord) (nx ny nz : ℝ) :
    - (2 : ℂ) * (normalizedPauliMatrix v).det =
        _root_.InfoGeometry.Physics.Section30UnifiedMatrixFramework.minkowskiForm
          v.t v.x v.y v.z ∧
      (blochMatrix nx ny nz).trace = 1 ∧
        (blochMatrix nx ny nz).det =
          ((1 : ℂ) - (nx : ℂ)^2 - (ny : ℂ)^2 - (nz : ℂ)^2) / 4 := by
  exact ⟨normalized_spacetime_det_readout v,
    bloch_density_trace nx ny nz,
    bloch_density_det nx ny nz⟩

end InfoGeometry.Physics.Section01MatrixBasisIntroduction

end noncomputable section
