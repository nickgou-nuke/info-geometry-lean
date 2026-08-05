import InfoGeometry.Physics.MD002FoundationalConventions

/-!
# Repaired MD 003: finite isomorphic representations and metrics

Source: `github-nick:nickgou-nuke/MD`, file `003.md`.

Chapter 3 states the core representation theorems of the handbook.  This file
formalizes the finite algebraic content that is already supported by the codebase:

* normalized Pauli matrices give the determinant/Minkowski interval convention;
* the trace form on normalized Pauli coordinates is the Euclidean dot product;
* coordinates are recovered by trace against the normalized Pauli axes;
* the quaternion norm shadow is the same Euclidean coordinate quadratic form;
* the complex biquaternion matrix representation has explicit coordinate readout
  and quaternion-unit multiplication table;
* the unnormalized soldering forms satisfy the explicit finite Fierz identity.

The broad claims that `ℍ_C ≃ M₂(ℂ)` as a packaged algebra isomorphism,
`Cl(1,3)` identifications, spinor-bundle constructions, or curved-spacetime
geometry are not asserted here.  The biquaternion material below is the explicit
finite Pauli-matrix representation and basis multiplication/readout table only.
Packaged algebra equivalence remains higher-level closure debt unless proved by
dedicated owners.
-/

noncomputable section

namespace InfoGeometry.Physics.MD003IsomorphicRepresentations

open Matrix BigOperators
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.MD002FoundationalConventions

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Trace bilinear readout `Tr(AB)` on the concrete `2 × 2` carrier. -/
def traceForm (A B : MatrixQuantumCarrier) : ℂ :=
  ∑ i : Fin 2, (A * B) i i

/-- The unnormalized Pauli axis indexed by `0,1,2,3`. -/
def sigmaAt : Fin 4 → MatrixQuantumCarrier
  | 0 => UnifiedMatrixBasis.I₂
  | 1 => UnifiedMatrixBasis.σ₁
  | 2 => UnifiedMatrixBasis.σ₂
  | 3 => UnifiedMatrixBasis.σ₃

/-- A normalized Pauli axis, with scalar `c` playing the algebraic role of `1 / sqrt 2`. -/
def normalizedAxis (c : ℂ) (a : Fin 4) : MatrixQuantumCarrier :=
  c • sigmaAt a

/-- Complex-coordinate Euclidean dot product for four components. -/
def coordDot (t x y z u v w r : ℂ) : ℂ :=
  t * u + x * v + y * w + z * r

/-- Quaternion norm shadow: the Euclidean quadratic form on coefficients. -/
def quaternionNormSq (t x y z : ℂ) : ℂ :=
  t * t + x * x + y * y + z * z

/-- Normalized determinant readout: `-2 det(dX)` is the `(-,+,+,+)` interval. -/
theorem md003_minkowski_metric_from_determinant
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    (-2 : ℂ) * Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
      -(dt * dt) + (dx * dx + dy * dy + dz * dz) :=
  normalized_interval_eq_minkowski_minus_plus_plus_plus c dt dx dy dz hc

/-- The normalized trace form is the coordinate Euclidean dot product. -/
theorem md003_trace_metric_eq_coordDot
    (c t x y z u v w r : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedPauliSpacetimeMatrix c t x y z)
      (normalizedPauliSpacetimeMatrix c u v w r) = coordDot t x y z u v w r := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  unfold traceForm normalizedPauliSpacetimeMatrix pauliSpacetimeMatrix coordDot
  simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
    UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring_nf
  rw [hc2]
  ring

/-- Trace recovers the time coordinate. -/
theorem md003_trace_recover_time
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedAxis c 0) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dt := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  unfold traceForm normalizedAxis normalizedPauliSpacetimeMatrix pauliSpacetimeMatrix sigmaAt
  simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
    UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  rw [hc2]
  ring

/-- Trace recovers the first spatial coordinate. -/
theorem md003_trace_recover_x
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedAxis c 1) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dx := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  unfold traceForm normalizedAxis normalizedPauliSpacetimeMatrix pauliSpacetimeMatrix sigmaAt
  simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
    UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  rw [hc2]
  ring

/-- Trace recovers the second spatial coordinate. -/
theorem md003_trace_recover_y
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedAxis c 2) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dy := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  unfold traceForm normalizedAxis normalizedPauliSpacetimeMatrix pauliSpacetimeMatrix sigmaAt
  simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
    UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring_nf
  rw [hc2]
  ring

/-- Trace recovers the third spatial coordinate. -/
theorem md003_trace_recover_z
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedAxis c 3) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dz := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  unfold traceForm normalizedAxis normalizedPauliSpacetimeMatrix pauliSpacetimeMatrix sigmaAt
  simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
    UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  rw [hc2]
  ring

/-- Quaternion norm shadow agrees with the normalized trace self-pairing. -/
theorem md003_quaternion_norm_eq_trace_self
    (c t x y z : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedPauliSpacetimeMatrix c t x y z)
      (normalizedPauliSpacetimeMatrix c t x y z) = quaternionNormSq t x y z := by
  simpa [quaternionNormSq, coordDot] using
    md003_trace_metric_eq_coordDot c t x y z t x y z hc

/-- Complex biquaternion matrix representation `q₀I - i qₖσₖ`. -/
def biquatMatrix (q0 q1 q2 q3 : ℂ) : MatrixQuantumCarrier :=
  q0 • UnifiedMatrixBasis.I₂ - (Complex.I * q1) • UnifiedMatrixBasis.σ₁ -
    (Complex.I * q2) • UnifiedMatrixBasis.σ₂ - (Complex.I * q3) • UnifiedMatrixBasis.σ₃

/-- Image of the scalar quaternion unit. -/
def biquatUnit0 : MatrixQuantumCarrier := biquatMatrix 1 0 0 0

/-- Image of the first quaternion unit. -/
def biquatUnit1 : MatrixQuantumCarrier := biquatMatrix 0 1 0 0

/-- Image of the second quaternion unit. -/
def biquatUnit2 : MatrixQuantumCarrier := biquatMatrix 0 0 1 0

/-- Image of the third quaternion unit. -/
def biquatUnit3 : MatrixQuantumCarrier := biquatMatrix 0 0 0 1

/-- The scalar unit maps to the identity matrix. -/
theorem biquatUnit0_eq_identity : biquatUnit0 = UnifiedMatrixBasis.I₂ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [biquatUnit0, biquatMatrix, UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁,
      UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃]

/-- The finite quaternion-unit multiplication table inside `M₂(ℂ)`. -/
theorem biquat_basis_multiplication_packet :
    biquatUnit1 * biquatUnit1 = -biquatUnit0 ∧
    biquatUnit2 * biquatUnit2 = -biquatUnit0 ∧
    biquatUnit3 * biquatUnit3 = -biquatUnit0 ∧
    biquatUnit1 * biquatUnit2 = biquatUnit3 ∧
    biquatUnit2 * biquatUnit3 = biquatUnit1 ∧
    biquatUnit3 * biquatUnit1 = biquatUnit2 := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [biquatUnit0, biquatUnit1, biquatMatrix, UnifiedMatrixBasis.I₂,
        UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃,
        Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [biquatUnit0, biquatUnit2, biquatMatrix, UnifiedMatrixBasis.I₂,
        UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃,
        Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [biquatUnit0, biquatUnit3, biquatMatrix, UnifiedMatrixBasis.I₂,
        UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃,
        Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [biquatUnit1, biquatUnit2, biquatUnit3, biquatMatrix,
        UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
        UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [biquatUnit1, biquatUnit2, biquatUnit3, biquatMatrix,
        UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
        UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [biquatUnit1, biquatUnit2, biquatUnit3, biquatMatrix,
        UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
        UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

/-- Trace against the Pauli basis recovers complex-biquaternion coordinates. -/
theorem biquat_trace_recover (q0 q1 q2 q3 : ℂ) :
    traceForm UnifiedMatrixBasis.I₂ (biquatMatrix q0 q1 q2 q3) / 2 = q0 ∧
    Complex.I * traceForm UnifiedMatrixBasis.σ₁ (biquatMatrix q0 q1 q2 q3) / 2 = q1 ∧
    Complex.I * traceForm UnifiedMatrixBasis.σ₂ (biquatMatrix q0 q1 q2 q3) / 2 = q2 ∧
    Complex.I * traceForm UnifiedMatrixBasis.σ₃ (biquatMatrix q0 q1 q2 q3) / 2 = q3 := by
  constructor
  · unfold traceForm biquatMatrix
    simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · unfold traceForm biquatMatrix
    simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    simp [Complex.I_sq]
  constructor
  · unfold traceForm biquatMatrix
    simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    simp [Complex.I_sq]
  · unfold traceForm biquatMatrix
    simp [UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    simp [Complex.I_sq]

/-- Spinor epsilon matrix used in the explicit finite Fierz check. -/
def epsilonSpinor : Fin 2 → Fin 2 → ℂ
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => -1
  | 1, 1 => 0

/-- Minkowski signs for `(-,+,+,+)` in Pauli-index form. -/
def minkowskiSign : Fin 4 → ℂ
  | 0 => -1
  | 1 => 1
  | 2 => 1
  | 3 => 1

/-- Unnormalized soldering-form contraction for the finite Fierz identity. -/
def unnormalizedSolderingContraction (A Ap B Bp : Fin 2) : ℂ :=
  ∑ a : Fin 4, minkowskiSign a * sigmaAt a A Ap * sigmaAt a B Bp

/-- Explicit finite Fierz identity for unnormalized Pauli soldering forms. -/
theorem md003_unnormalized_fierz_identity (A Ap B Bp : Fin 2) :
    unnormalizedSolderingContraction A Ap B Bp =
      -2 * epsilonSpinor A B * epsilonSpinor Ap Bp := by
  fin_cases A <;> fin_cases Ap <;> fin_cases B <;> fin_cases Bp <;>
    simp [unnormalizedSolderingContraction, minkowskiSign, sigmaAt, epsilonSpinor,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Fin.sum_univ_four] <;> norm_num

end InfoGeometry.Physics.MD003IsomorphicRepresentations

end noncomputable section
