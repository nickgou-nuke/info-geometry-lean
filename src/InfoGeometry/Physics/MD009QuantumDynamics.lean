import InfoGeometry.Physics.MD003IsomorphicRepresentations
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Repaired MD 009: finite quantum-dynamics algebra

Source: `github-nick:nickgou-nuke/MD`, file `009.md`.

Chapter 9 discusses canonical position/momentum operators, matrix CCRs,
quaternion derivative conventions, Hilbert spaces, Schrödinger/Heisenberg
pictures, and path-integral/propagator outlines.  The continuum claims require
unbounded operators, domains, differentiability, Hilbert-space analysis, and
measure theory, so this owner extracts only the finite algebraic socket:

* normalized Pauli completeness behind the matrix CCR coefficient;
* transport of a vector CCR Kronecker table through the Pauli soldering forms;
* finite quaternion-derivative normalization readouts explaining the factors
  `2`, `4`, and `1` under the conventions discussed in the source.

No theorem here asserts PDEs, self-adjointness, unitarity of exponentials,
Schrödinger/Heisenberg equations, Hilbert-space isomorphisms, translation
semigroups, propagators, or path integrals.
-/

noncomputable section

namespace InfoGeometry.Physics.MD009QuantumDynamics

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators
open InfoGeometry.Physics.MD002FoundationalConventions
open InfoGeometry.Physics.MD003IsomorphicRepresentations

/-- Kronecker delta on spinor indices as a complex scalar. -/
def delta2 (i j : Fin 2) : ℂ :=
  if i = j then 1 else 0

/-- Kronecker delta on four-vector indices as a complex scalar. -/
def delta4 (i j : Fin 4) : ℂ :=
  if i = j then 1 else 0

/-- Normalized Pauli matrix coefficient with abstract normalization scalar `c`. -/
def normalizedSigmaCoeff (c : ℂ) (a : Fin 4) (i j : Fin 2) : ℂ :=
  c * sigmaAt a i j

/-- Finite Pauli completeness coefficient used in the matrix CCR derivation. -/
def pauliCompletenessCoeff (c : ℂ) (A Ap B Bp : Fin 2) : ℂ :=
  ∑ a : Fin 4, normalizedSigmaCoeff c a A Ap * normalizedSigmaCoeff c a Bp B

/--
Normalized Pauli completeness:
`∑ₐ σ̂ᵃ_{A A'} σ̂ᵃ_{B' B} = δ_{A B} δ_{A' B'}`.
-/
theorem normalized_pauli_completeness (c : ℂ) (hc : IsPauliNormalization c)
    (A Ap B Bp : Fin 2) :
    pauliCompletenessCoeff c A Ap B Bp = delta2 A B * delta2 Ap Bp := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  fin_cases A <;> fin_cases Ap <;> fin_cases B <;> fin_cases Bp <;>
    simp [pauliCompletenessCoeff, normalizedSigmaCoeff, sigmaAt, delta2,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Fin.sum_univ_four]
    <;> ring_nf
    <;> rw [hc2]
    <;> norm_num

/-- Vector CCR coefficient table, with `ihbar` standing for the scalar `iℏ`. -/
def vectorCCRCoeff (ihbar : ℂ) (a b : Fin 4) : ℂ :=
  ihbar * delta4 a b

/-- Matrix CCR coefficient obtained by soldering the vector CCR table. -/
def matrixCCRCoeff (c ihbar : ℂ) (A Ap B Bp : Fin 2) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    normalizedSigmaCoeff c a A Ap * normalizedSigmaCoeff c b Bp B * vectorCCRCoeff ihbar a b

/-- The finite matrix-CCR coefficient reduces to `ihbar δ_A^B δ_A'^B'`. -/
theorem matrix_ccr_coefficient (c ihbar : ℂ) (hc : IsPauliNormalization c)
    (A Ap B Bp : Fin 2) :
    matrixCCRCoeff c ihbar A Ap B Bp = ihbar * delta2 A B * delta2 Ap Bp := by
  have hc2 : c ^ 2 = (1 / 2 : ℂ) := by
    simpa [IsPauliNormalization, pow_two] using hc
  unfold matrixCCRCoeff vectorCCRCoeff delta4
  fin_cases A <;> fin_cases Ap <;> fin_cases B <;> fin_cases Bp <;>
    simp [normalizedSigmaCoeff, sigmaAt, delta2,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃, Fin.sum_univ_four]
    <;> ring_nf
    <;> rw [hc2]
    <;> simp [Complex.I_sq]
    <;> ring_nf

/-- Formal quaternion basis-square table for the derivative normalization discussion. -/
def quaternionBasisSquare : Fin 4 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1

/-- The standard Moisil--Teodoresco-style normalization gives `D_q q = 2`. -/
def standardQuaternionDerivativeOnQ : ℝ :=
  (1 / 2 : ℝ) * (quaternionBasisSquare 0 -
    quaternionBasisSquare 1 - quaternionBasisSquare 2 - quaternionBasisSquare 3)

/-- Dropping the factor `1/2` gives `4`. -/
def unscaledQuaternionDerivativeOnQ : ℝ :=
  quaternionBasisSquare 0 - quaternionBasisSquare 1 -
    quaternionBasisSquare 2 - quaternionBasisSquare 3

/-- Scaling the standard derivative by `1/2` gives the canonical scalar `1`. -/
def canonicallyScaledQuaternionDerivativeOnQ : ℝ :=
  (1 / 2 : ℝ) * standardQuaternionDerivativeOnQ

/-- Standard quaternion derivative readout from the source: `D_q q = 2`. -/
theorem standardQuaternionDerivativeOnQ_eq_two :
    standardQuaternionDerivativeOnQ = 2 := by
  norm_num [standardQuaternionDerivativeOnQ, quaternionBasisSquare]

/-- Unscaled derivative convention readout: `D'_q q = 4`. -/
theorem unscaledQuaternionDerivativeOnQ_eq_four :
    unscaledQuaternionDerivativeOnQ = 4 := by
  norm_num [unscaledQuaternionDerivativeOnQ, quaternionBasisSquare]

/-- Canonically scaled derivative readout: `(1/2)D_q q = 1`. -/
theorem canonicallyScaledQuaternionDerivativeOnQ_eq_one :
    canonicallyScaledQuaternionDerivativeOnQ = 1 := by
  norm_num [canonicallyScaledQuaternionDerivativeOnQ, standardQuaternionDerivativeOnQ_eq_two]

/-- Repaired theorem-safe Chapter 9 finite dynamics packet. -/
theorem repaired_MD009_quantum_dynamics_packet (c ihbar : ℂ) (hc : IsPauliNormalization c) :
    (∀ A Ap B Bp : Fin 2,
      pauliCompletenessCoeff c A Ap B Bp = delta2 A B * delta2 Ap Bp) ∧
    (∀ A Ap B Bp : Fin 2,
      matrixCCRCoeff c ihbar A Ap B Bp = ihbar * delta2 A B * delta2 Ap Bp) ∧
    standardQuaternionDerivativeOnQ = 2 ∧
    unscaledQuaternionDerivativeOnQ = 4 ∧
    canonicallyScaledQuaternionDerivativeOnQ = 1 := by
  exact ⟨fun A Ap B Bp => normalized_pauli_completeness c hc A Ap B Bp,
    fun A Ap B Bp => matrix_ccr_coefficient c ihbar hc A Ap B Bp,
    standardQuaternionDerivativeOnQ_eq_two,
    unscaledQuaternionDerivativeOnQ_eq_four,
    canonicallyScaledQuaternionDerivativeOnQ_eq_one⟩

end InfoGeometry.Physics.MD009QuantumDynamics

end noncomputable section
