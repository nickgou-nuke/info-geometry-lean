import Mathlib
import InfoGeometry.Physics.MD006OperatorEigenoperators

/-!
# Repaired MD 007: finite quantum eigenoperator interpretation

Source: `github-nick:nickgou-nuke/MD`, file `007.md`.

Chapter 7 interprets the matrix-unit/eigenoperator basis as qubit projectors,
transition operators, measurements, dynamics, and channels.  This file proves
the finite algebraic identities behind that interpretation:

* computational-basis outer products are the matrix units `Eᵢⱼ`;
* every `2 × 2` operator decomposes into matrix units with its entries;
* trace expectations `Tr(Eᵢⱼ ρ)` read the transposed matrix entries;
* Pauli observables decompose in the `Eᵢⱼ` basis;
* projective/Lüders numerators and diagonal weak-measurement numerators reduce
  to explicit matrix-unit coefficients;
* the finite depolarizing-channel formula acts on `Eᵢⱼ` as expected.

No theorem here asserts positivity, CPTP/complete positivity, Born-rule physics,
continuous unitary time evolution, exponentials, or any physical measurement
law beyond these finite identities.
-/

noncomputable section

namespace InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.MD006OperatorEigenoperators

/-- Computational basis ket `|1⟩`. -/
def ket1 : Fin 2 → ℂ
  | 0 => 1
  | 1 => 0

/-- Computational basis ket `|2⟩`. -/
def ket2 : Fin 2 → ℂ
  | 0 => 0
  | 1 => 1

/-- Finite outer product `|v⟩⟨w|` for the computational basis. -/
def outer (v w : Fin 2 → ℂ) : MatrixQuantumCarrier :=
  fun i j => v i * w j

/-- `|1⟩⟨1| = E₁₁`. -/
theorem outer_ket1_ket1 : outer ket1 ket1 = E11 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [outer, ket1, E11]

/-- `|1⟩⟨2| = E₁₂`. -/
theorem outer_ket1_ket2 : outer ket1 ket2 = E12 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [outer, ket1, ket2, E12]

/-- `|2⟩⟨1| = E₂₁`. -/
theorem outer_ket2_ket1 : outer ket2 ket1 = E21 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [outer, ket1, ket2, E21]

/-- `|2⟩⟨2| = E₂₂`. -/
theorem outer_ket2_ket2 : outer ket2 ket2 = E22 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [outer, ket2, E22]

/-- Matrix trace on the concrete `2 × 2` carrier. -/
def trace2 (A : MatrixQuantumCarrier) : ℂ :=
  ∑ i : Fin 2, A i i

/-- Every `2 × 2` operator decomposes into the eigenoperator basis by entries. -/
theorem operator_decompose (A : MatrixQuantumCarrier) :
    A = A 0 0 • E11 + A 0 1 • E12 + A 1 0 • E21 + A 1 1 • E22 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E11, E12, E21, E22]

/-- Coefficients are recovered by trace against transposed matrix units. -/
theorem coefficient_trace_recover (A : MatrixQuantumCarrier) :
    trace2 (E11 * A) = A 0 0 ∧
    trace2 (E21 * A) = A 0 1 ∧
    trace2 (E12 * A) = A 1 0 ∧
    trace2 (E22 * A) = A 1 1 := by
  constructor
  · simp [trace2, E11, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · simp [trace2, E21, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · simp [trace2, E12, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [trace2, E22, Matrix.mul_apply, Fin.sum_univ_two]

/-- Expectation readout of a matrix unit against a state matrix. -/
def expectation (E ρ : MatrixQuantumCarrier) : ℂ :=
  trace2 (E * ρ)

/-- `⟨E₁₁⟩_ρ = ρ₁₁`. -/
theorem expectation_E11 (ρ : MatrixQuantumCarrier) : expectation E11 ρ = ρ 0 0 :=
  (coefficient_trace_recover ρ).1

/-- `⟨E₂₁⟩_ρ = ρ₁₂`. -/
theorem expectation_E21 (ρ : MatrixQuantumCarrier) : expectation E21 ρ = ρ 0 1 :=
  (coefficient_trace_recover ρ).2.1

/-- `⟨E₁₂⟩_ρ = ρ₂₁`. -/
theorem expectation_E12 (ρ : MatrixQuantumCarrier) : expectation E12 ρ = ρ 1 0 :=
  (coefficient_trace_recover ρ).2.2.1

/-- `⟨E₂₂⟩_ρ = ρ₂₂`. -/
theorem expectation_E22 (ρ : MatrixQuantumCarrier) : expectation E22 ρ = ρ 1 1 :=
  (coefficient_trace_recover ρ).2.2.2

/-- Identity decomposes as the sum of basis projectors. -/
theorem identity_eigenoperator_decomposition :
    UnifiedMatrixBasis.I₂ = E11 + E22 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [UnifiedMatrixBasis.I₂, E11, E22]

/-- `σ₁ = E₁₂ + E₂₁`. -/
theorem sigma1_eigenoperator_decomposition :
    UnifiedMatrixBasis.σ₁ = E12 + E21 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [UnifiedMatrixBasis.σ₁, E12, E21]

/-- `σ₂ = -i(E₁₂ - E₂₁)`. -/
theorem sigma2_eigenoperator_decomposition :
    UnifiedMatrixBasis.σ₂ = (-Complex.I : ℂ) • (E12 - E21) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [UnifiedMatrixBasis.σ₂, E12, E21]

/-- `σ₃ = E₁₁ - E₂₂`. -/
theorem sigma3_eigenoperator_decomposition :
    UnifiedMatrixBasis.σ₃ = E11 - E22 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [UnifiedMatrixBasis.σ₃, E11, E22]

/-- Projective numerator for outcome `1`: `E₁₁ ρ E₁₁ = ρ₁₁ E₁₁`. -/
theorem luders_numerator_E11 (ρ : MatrixQuantumCarrier) :
    E11 * ρ * E11 = ρ 0 0 • E11 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E11, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Projective numerator for outcome `2`: `E₂₂ ρ E₂₂ = ρ₂₂ E₂₂`. -/
theorem luders_numerator_E22 (ρ : MatrixQuantumCarrier) :
    E22 * ρ * E22 = ρ 1 1 • E22 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E22, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Diagonal Kraus operator `a E₁₁ + b E₂₂`. -/
def diagonalKraus (a b : ℂ) : MatrixQuantumCarrier :=
  a • E11 + b • E22

/-- The diagonal weak-measurement numerator in matrix-unit coordinates. -/
theorem diagonalKraus_numerator (a b : ℂ) (ρ : MatrixQuantumCarrier) :
    diagonalKraus a b * ρ * diagonalKraus a b =
      (a * a * ρ 0 0) • E11 + (a * b * ρ 0 1) • E12 +
      (b * a * ρ 1 0) • E21 + (b * b * ρ 1 1) • E22 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagonalKraus, E11, E12, E21, E22, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
    <;> ring

/-- Finite depolarizing channel formula on arbitrary `2 × 2` matrices. -/
def depolarizingChannel (p : ℂ) (A : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  (1 - p) • A + ((p / 2) * trace2 A) • UnifiedMatrixBasis.I₂

/-- Depolarizing channel on `E₁₁`. -/
theorem depolarizing_E11 (p : ℂ) :
    depolarizingChannel p E11 = (1 - p / 2) • E11 + (p / 2) • E22 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [depolarizingChannel, trace2, E11, E22, UnifiedMatrixBasis.I₂, Fin.sum_univ_two]
    <;> ring

/-- Depolarizing channel on `E₂₂`. -/
theorem depolarizing_E22 (p : ℂ) :
    depolarizingChannel p E22 = (p / 2) • E11 + (1 - p / 2) • E22 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [depolarizingChannel, trace2, E11, E22, UnifiedMatrixBasis.I₂, Fin.sum_univ_two]
    <;> ring

/-- Depolarizing channel damps `E₁₂` by `1-p`. -/
theorem depolarizing_E12 (p : ℂ) :
    depolarizingChannel p E12 = (1 - p) • E12 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [depolarizingChannel, trace2, E12, UnifiedMatrixBasis.I₂, Fin.sum_univ_two]
    <;> ring

/-- Depolarizing channel damps `E₂₁` by `1-p`. -/
theorem depolarizing_E21 (p : ℂ) :
    depolarizingChannel p E21 = (1 - p) • E21 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [depolarizingChannel, trace2, E21, UnifiedMatrixBasis.I₂, Fin.sum_univ_two]
    <;> ring

/-- Repaired theorem-safe Chapter 7 finite quantum/eigenoperator packet. -/
theorem repaired_MD007_quantum_eigenoperator_packet (ρ : MatrixQuantumCarrier) (p : ℂ) :
    outer ket1 ket1 = E11 ∧
    outer ket1 ket2 = E12 ∧
    ρ = ρ 0 0 • E11 + ρ 0 1 • E12 + ρ 1 0 • E21 + ρ 1 1 • E22 ∧
    expectation E11 ρ = ρ 0 0 ∧
    expectation E12 ρ = ρ 1 0 ∧
    E11 * ρ * E11 = ρ 0 0 • E11 ∧
    UnifiedMatrixBasis.σ₁ = E12 + E21 ∧
    depolarizingChannel p E12 = (1 - p) • E12 := by
  exact ⟨outer_ket1_ket1, outer_ket1_ket2, operator_decompose ρ,
    expectation_E11 ρ, expectation_E12 ρ, luders_numerator_E11 ρ,
    sigma1_eigenoperator_decomposition, depolarizing_E12 p⟩

end InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation

end noncomputable section
