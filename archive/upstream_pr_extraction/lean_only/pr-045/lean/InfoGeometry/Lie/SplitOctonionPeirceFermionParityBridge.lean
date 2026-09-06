import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading

/-!
# Peirce-defect fermion parity on the split-octonion carrier

The normalized commutator with the distinguished split axis is already an
intrinsic tripotent operator on the genuine `uPlus/uMinus` Peirce basis.  This
owner records its idempotent square and the associated two-valued parity.

The word `fermion` here is deliberately qualified: this is the Peirce-defect
occupation projector, not the standard exterior-degree parity and not an
analytic Witten index.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge

open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev Carrier := InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.CanonicalZorn
abbrev CarrierEnd := Module.End ℝ Carrier

/-- The normalized Peirce defect, equal to one half of the vacuum commutator. -/
def peirceDefectOperator : CarrierEnd := axialGrading

/-- The defect is the normalized regular left-minus-right commutator for the
distinguished split axis.  The factor `1 / 2` is essential: the raw
commutator has eigenvalues `0, ±2`, while the tripotent defect has eigenvalues
`0, ±1`. -/
theorem peirceDefectOperator_eq_normalized_left_sub_right :
    peirceDefectOperator =
      (1 / 2 : ℝ) •
        (leftMultiplication InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit -
          rightMultiplication InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) := by
  rw [peirceDefectOperator, axialGrading, ellCommutator_eq_left_sub_right]

/- The raw regular commutator is twice the tripotent Peirce defect.  This
is the normalization needed when comparing the `0, ±2` regular spectrum with
the `0, ±1` tripotent spectrum. -/
theorem left_sub_right_eq_two_peirceDefectOperator :
    leftMultiplication InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit -
        rightMultiplication InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit =
      (2 : ℝ) • peirceDefectOperator := by
  rw [peirceDefectOperator_eq_normalized_left_sub_right]
  module

/-- The Peirce-defect occupation projector `F_P = A²`. -/
def peirceFermionNumber : CarrierEnd := peirceDefectOperator * peirceDefectOperator

/-- The associated two-valued Peirce parity `I - 2 F_P`. -/
def peirceWittenParity : CarrierEnd :=
  (1 : CarrierEnd) - (2 : ℝ) • peirceFermionNumber

theorem peirceDefect_tripotent :
    peirceDefectOperator ^ 3 = peirceDefectOperator := by
  simpa [peirceDefectOperator] using axialGrading_tripotent

theorem peirceFermionNumber_idempotent :
    peirceFermionNumber * peirceFermionNumber = peirceFermionNumber := by
  change (axialGrading * axialGrading) * (axialGrading * axialGrading) =
    axialGrading * axialGrading
  calc
    (axialGrading * axialGrading) * (axialGrading * axialGrading) =
        axialGrading ^ 3 * axialGrading := by
          noncomm_ring
    _ = axialGrading * axialGrading := by rw [axialGrading_tripotent]

theorem peirceWittenParity_eq_zeroReflection :
    peirceWittenParity =
      (2 : ℝ) • axialProjectorZero - (1 : CarrierEnd) := by
  change (1 : CarrierEnd) - (2 : ℝ) • (axialGrading * axialGrading) =
    (2 : ℝ) • ((LinearMap.id : CarrierEnd) - axialGrading ^ 2) -
      (1 : CarrierEnd)
  simp only [pow_two]
  module

theorem peirceWittenParity_basis (i : Fin 8) :
    peirceWittenParity
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i) =
      (1 - 2 * (axialWeight i) ^ 2) •
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i := by
  rw [peirceWittenParity_eq_zeroReflection]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [axialProjectorZero_basis]
  change (2 : ℝ) • ((1 - (axialWeight i) ^ 2) •
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i) -
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i = _
  rw [smul_smul]
  module

theorem peirceWittenParity_sq :
    peirceWittenParity * peirceWittenParity = (1 : CarrierEnd) := by
  apply InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, peirceWittenParity_basis, map_smul,
    peirceWittenParity_basis]
  fin_cases i <;> norm_num [axialWeight]

theorem peirceWittenParity_eq_tripotent_zero_reflection :
    peirceWittenParity =
      (2 : ℝ) • axialProjectorZero - (1 : CarrierEnd) :=
  peirceWittenParity_eq_zeroReflection

theorem peirceDefect_zero_projector_eq_axialProjectorZero :
    (1 : CarrierEnd) - peirceFermionNumber = axialProjectorZero := by
  change (LinearMap.id : CarrierEnd) - axialGrading ^ 2 = axialProjectorZero
  rfl

/-- The occupation projector is exactly the sum of the two nonzero
Peirce eigenspace projectors. -/
theorem peirceFermionNumber_eq_axialProjectors_nonzero :
    peirceFermionNumber = axialProjectorPlus + axialProjectorMinus := by
  change axialGrading ^ 2 = axialProjectorPlus + axialProjectorMinus
  exact (axialProjectors_add_nonzero_eq_axialGrading_sq).symm

theorem peirceZeroProjector_eq_axialProjectorZero :
    (1 : CarrierEnd) - peirceFermionNumber = axialProjectorZero :=
  peirceDefect_zero_projector_eq_axialProjectorZero

end InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge
