import InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime

/-!
# Section 33 repaired: Pauli completion and finite biquaternion socket

The source repeats the Section 32 quaternionic-emergent-spacetime program and
adds much stronger continuum/phenomenological claims.  This repaired file keeps
only finite algebraic content:

* the Pauli matrices plus identity decompose every `2 × 2` complex matrix;
* radius-`r` Bloch density matrices are idempotent under the algebraic unit
  condition `r²‖n‖² = 1`;
* the same condition gives the determinant-zero/null-boundary certificate from
  Section 32;
* a biquaternion is represented theorem-safely as a pair of finite Pauli
  matrices, with a checked dual-swap involution.

No Dirac-equation equivalence, Einstein equation, torsion-from-spin theorem,
entanglement/connection theorem, holographic area law, black-hole entropy
correction, gravitational-wave equation, or experimental prediction is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.Section33PauliBiquaternionCompletion

open Matrix Complex
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime

/-! ## Pauli basis completion for all `2 × 2` complex matrices -/

/-- Scalar/identity coefficient in the Pauli decomposition. -/
def pauliCoeff0 (A : Mat2) : ℂ :=
  (A 0 0 + A 1 1) / 2

/-- `σ₁` coefficient in the Pauli decomposition. -/
def pauliCoeff1 (A : Mat2) : ℂ :=
  (A 0 1 + A 1 0) / 2

/-- `σ₂` coefficient in the Pauli decomposition. -/
def pauliCoeff2 (A : Mat2) : ℂ :=
  (Complex.I / 2) * (A 0 1 - A 1 0)

/-- `σ₃` coefficient in the Pauli decomposition. -/
def pauliCoeff3 (A : Mat2) : ℂ :=
  (A 0 0 - A 1 1) / 2

/-- Recompose a matrix from its Pauli coefficients. -/
def pauliRecompose (A : Mat2) : Mat2 :=
  pauliCoeff0 A • σ0 + pauliCoeff1 A • σ1 +
    pauliCoeff2 A • σ2 + pauliCoeff3 A • σ3

/-- Every `2 × 2` complex matrix is recovered from the Pauli-basis coefficients. -/
theorem pauli_recompose_eq_self (A : Mat2) :
    pauliRecompose A = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliRecompose, pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
      σ0, σ1, σ2, σ3]
  all_goals ring_nf
  all_goals rw [complex_I_sq]
  all_goals ring

/-- Trace readback: the scalar Pauli coefficient is half the matrix trace. -/
theorem pauliCoeff0_eq_trace_div_two (A : Mat2) :
    pauliCoeff0 A = A.trace / 2 := by
  simp [pauliCoeff0, Matrix.trace, Fin.sum_univ_two]

/-! ## Repaired pure/null finite boundary -/

/-- Algebraic unit Bloch vector gives an idempotent density matrix. -/
theorem densityMatrix_idempotent_of_unit (a b c : ℂ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    densityMatrix a b c * densityMatrix a b c = densityMatrix a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [densityMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · ring_nf at hunit ⊢
    rw [complex_I_sq]
    ring_nf
    linear_combination hunit / 4
  · ring
  · ring
  · ring_nf at hunit ⊢
    rw [complex_I_sq]
    ring_nf
    linear_combination hunit / 4

/-- Radius-`r` Bloch density is idempotent when `r²‖n‖² = 1`. -/
theorem blochDensityAtRadius_idempotent_of_scaled_unit (r n1 n2 n3 : ℂ)
    (hunit : r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2) = 1) :
    blochDensityAtRadius r n1 n2 n3 * blochDensityAtRadius r n1 n2 n3 =
      blochDensityAtRadius r n1 n2 n3 := by
  have hscaled : (r * n1) ^ 2 + (r * n2) ^ 2 + (r * n3) ^ 2 = 1 := by
    rw [show (r * n1) ^ 2 + (r * n2) ^ 2 + (r * n3) ^ 2 =
      r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2) by ring]
    exact hunit
  simpa [blochDensityAtRadius] using
    densityMatrix_idempotent_of_unit (r * n1) (r * n2) (r * n3) hscaled

/-- The same scaled-unit condition forces the density determinant to vanish. -/
theorem blochDensityAtRadius_det_zero_of_scaled_unit (r n1 n2 n3 : ℂ)
    (hunit : r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2) = 1) :
    (blochDensityAtRadius r n1 n2 n3).det = 0 := by
  rw [blochDensityAtRadius, densityMatrix_det]
  rw [show (r * n1) ^ 2 + (r * n2) ^ 2 + (r * n3) ^ 2 =
    r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2) by ring]
  rw [hunit]
  ring

/-- Scaled-unit boundary also gives determinant zero for the Section 32 spacetime point. -/
theorem blochSpacetimePoint_det_zero_of_scaled_unit (t r n1 n2 n3 : ℂ)
    (hunit : r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2) = 1) :
    (blochSpacetimePoint t r n1 n2 n3).det = 0 := by
  rw [blochSpacetimePoint_det, hunit]
  ring

/-! ## Finite biquaternion-pair socket -/

/-- The theorem-safe finite shadow of a biquaternion: two Pauli-matrix parts. -/
structure BiquaternionPair where
  primal : Mat2
  dual : Mat2

/-- Swap the two finite Pauli components. -/
def dualSwap (q : BiquaternionPair) : BiquaternionPair :=
  { primal := q.dual, dual := q.primal }

/-- The dual swap is an involution. -/
theorem dualSwap_involutive (q : BiquaternionPair) :
    dualSwap (dualSwap q) = q := by
  cases q
  rfl

/-- Recompose both parts of a biquaternion pair from Pauli coefficients. -/
def pauliRecomposePair (q : BiquaternionPair) : BiquaternionPair :=
  { primal := pauliRecompose q.primal, dual := pauliRecompose q.dual }

/-- Pauli recomposition fixes both parts of a finite biquaternion pair. -/
theorem pauliRecomposePair_eq_self (q : BiquaternionPair) :
    pauliRecomposePair q = q := by
  cases q
  simp [pauliRecomposePair, pauli_recompose_eq_self]

/-- Repaired Section 33 packet: basis completion, pure density, and null boundary. -/
theorem repaired_section33_pauli_biquaternion_packet
    (A : Mat2) (t r n1 n2 n3 : ℂ)
    (hunit : r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2) = 1) :
    pauliRecompose A = A ∧
    blochDensityAtRadius r n1 n2 n3 * blochDensityAtRadius r n1 n2 n3 =
      blochDensityAtRadius r n1 n2 n3 ∧
    (blochSpacetimePoint t r n1 n2 n3).det = 0 := by
  exact ⟨pauli_recompose_eq_self A,
    blochDensityAtRadius_idempotent_of_scaled_unit r n1 n2 n3 hunit,
    blochSpacetimePoint_det_zero_of_scaled_unit t r n1 n2 n3 hunit⟩

end InfoGeometry.Physics.Section33PauliBiquaternionCompletion

end noncomputable section
