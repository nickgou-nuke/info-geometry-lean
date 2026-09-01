import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularAxialGrading
import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

/-!
# Genuine circular chiral eigenstates, projectors, parity, and grading

This owner uses the genuine circular Peirce basis with complementary
idempotents `uPlus` and `uMinus`.  It deliberately does not identify this basis
with the distinct diagonal `zornPlus/zornMinus` circular convention.

The eight chiral labels are read as

* `P+  -> uPlus`,
* `S+ᵢ -> rootPlus i`,
* `P-  -> uMinus`,
* `S-ᵢ -> rootMinus i`.

Two commuting pieces of spectral data are kept distinct:

* chiral parity has eigenvalue `+1` on the full plus half and `-1` on the full
  minus half;
* the normalized axial grading has eigenvalues `0,+1,-1`, with the two Peirce
  idempotents in weight zero and the root channels in weights `±1`.

The free associative chiral envelope is lifted to native linear operators by
left multiplication by these genuine circular basis states.  No claim is made
that these left-multiplication operators are eigenoperators of an adjoint
superoperator; the proved eigenvalue statements are on the underlying circular
states.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionChiralCircularSpectralBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularAxialGrading

abbrev CZ := CanonicalZorn

/-- Canonical index of the eight chiral labels in the genuine circular basis. -/
def generatorIndex : ChiralGenerator → Fin 8
  | .pPlus => 0
  | .sPlus 0 => 1
  | .sPlus 1 => 2
  | .sPlus 2 => 3
  | .pMinus => 4
  | .sMinus 0 => 5
  | .sMinus 1 => 6
  | .sMinus 2 => 7

/-- Genuine circular state attached to a chiral generator label. -/
def generatorState (g : ChiralGenerator) : CZ :=
  circularPeirceBasis (generatorIndex g)

@[simp] theorem generatorState_pPlus : generatorState .pPlus = uPlus := by
  simp [generatorState, generatorIndex, circularPeirceBasis_zero]

@[simp] theorem generatorState_pMinus : generatorState .pMinus = uMinus := by
  simp [generatorState, generatorIndex, circularPeirceBasis_four]

@[simp] theorem generatorState_sPlus (i : Fin 3) :
    generatorState (.sPlus i) = rootPlus i := by
  fin_cases i <;> simp [generatorState, generatorIndex,
    circularPeirceBasis_one, circularPeirceBasis_two, circularPeirceBasis_three]

@[simp] theorem generatorState_sMinus (i : Fin 3) :
    generatorState (.sMinus i) = rootMinus i := by
  fin_cases i <;> simp [generatorState, generatorIndex,
    circularPeirceBasis_five, circularPeirceBasis_six, circularPeirceBasis_seven]

/-- The formal envelope degree is exactly the genuine circular axial weight. -/
theorem axialWeight_generatorIndex (g : ChiralGenerator) :
    axialWeight (generatorIndex g) = (generatorDegree g : ℝ) := by
  cases g with
  | pPlus => simp [generatorIndex, axialWeight, generatorDegree]
  | pMinus => simp [generatorIndex, axialWeight, generatorDegree]
  | sPlus i => fin_cases i <;> norm_num [generatorIndex, axialWeight, generatorDegree]
  | sMinus i => fin_cases i <;> norm_num [generatorIndex, axialWeight, generatorDegree]

/-- Every chiral circular state is an eigenstate of the normalized axial grading. -/
theorem generatorState_axial_eigen (g : ChiralGenerator) :
    axialGrading (generatorState g) =
      (generatorDegree g : ℝ) • generatorState g := by
  rw [generatorState, axialGrading_basis, axialWeight_generatorIndex]

/-- Equivalent eigenspace formulation of the axial selection rule. -/
theorem generatorState_mem_axial_eigenspace (g : ChiralGenerator) :
    generatorState g ∈
      Module.End.eigenspace axialGrading (generatorDegree g : ℝ) := by
  rw [Module.End.mem_eigenspace_iff]
  exact generatorState_axial_eigen g

/-- Plus Peirce projector on the genuine circular carrier. -/
noncomputable def chiralPPlus : Module.End ℝ CZ :=
  leftMultiplication uPlus

/-- Minus Peirce projector on the genuine circular carrier. -/
noncomputable def chiralPMinus : Module.End ℝ CZ :=
  leftMultiplication uMinus

/-- Chiral parity/grading involution. -/
noncomputable def chiralParity : Module.End ℝ CZ :=
  chiralPPlus - chiralPMinus

/-- Parity eigenvalue of each circular basis state. -/
def parityWeight : Fin 8 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => -1
  | 5 => -1
  | 6 => -1
  | 7 => -1

/-- The plus projector is diagonal on the genuine circular basis. -/
theorem chiralPPlus_basis (i : Fin 8) :
    chiralPPlus (circularPeirceBasis i) =
      if i.val < 4 then circularPeirceBasis i else 0 := by
  fin_cases i <;>
    simp [chiralPPlus, circularPeirceBasis_apply, frame,
      leftMultiplication_uPlus_frame]

/-- The minus projector is diagonal on the genuine circular basis. -/
theorem chiralPMinus_basis (i : Fin 8) :
    chiralPMinus (circularPeirceBasis i) =
      if 4 ≤ i.val then circularPeirceBasis i else 0 := by
  fin_cases i <;>
    simp [chiralPMinus, circularPeirceBasis_apply, frame,
      leftMultiplication_uMinus_frame]

/-- The two chiral projectors are complementary. -/
theorem chiralPPlus_add_chiralPMinus :
    chiralPPlus + chiralPMinus = (1 : Module.End ℝ CZ) := by
  apply circularPeirceBasis.ext
  intro i
  fin_cases i <;>
    simp [chiralPPlus, chiralPMinus, circularPeirceBasis_apply, frame,
      leftMultiplication_uPlus_frame, leftMultiplication_uMinus_frame]

/-- Plus chirality projector is idempotent as a linear operator. -/
theorem chiralPPlus_idempotent : chiralPPlus * chiralPPlus = chiralPPlus := by
  apply circularPeirceBasis.ext
  intro i
  fin_cases i <;>
    simp [chiralPPlus, Module.End.mul_apply, circularPeirceBasis_apply, frame,
      leftMultiplication_uPlus_frame]

/-- Minus chirality projector is idempotent as a linear operator. -/
theorem chiralPMinus_idempotent : chiralPMinus * chiralPMinus = chiralPMinus := by
  apply circularPeirceBasis.ext
  intro i
  fin_cases i <;>
    simp [chiralPMinus, Module.End.mul_apply, circularPeirceBasis_apply, frame,
      leftMultiplication_uMinus_frame]

/-- The two chiral projectors are orthogonal in operator composition. -/
theorem chiralPPlus_mul_chiralPMinus : chiralPPlus * chiralPMinus = 0 := by
  apply circularPeirceBasis.ext
  intro i
  fin_cases i <;>
    simp [chiralPPlus, chiralPMinus, Module.End.mul_apply,
      circularPeirceBasis_apply, frame, leftMultiplication_uPlus_frame,
      leftMultiplication_uMinus_frame]

/-- Reverse orthogonality of the two chiral projectors. -/
theorem chiralPMinus_mul_chiralPPlus : chiralPMinus * chiralPPlus = 0 := by
  apply circularPeirceBasis.ext
  intro i
  fin_cases i <;>
    simp [chiralPPlus, chiralPMinus, Module.End.mul_apply,
      circularPeirceBasis_apply, frame, leftMultiplication_uPlus_frame,
      leftMultiplication_uMinus_frame]

/-- Every genuine circular basis state is a parity eigenstate. -/
theorem chiralParity_basis (i : Fin 8) :
    chiralParity (circularPeirceBasis i) =
      parityWeight i • circularPeirceBasis i := by
  fin_cases i <;>
    simp [chiralParity, chiralPPlus, chiralPMinus, parityWeight,
      circularPeirceBasis_apply, frame, leftMultiplication_uPlus_frame,
      leftMultiplication_uMinus_frame]

/-- The chiral parity operator is an involution. -/
theorem chiralParity_sq : chiralParity * chiralParity = (1 : Module.End ℝ CZ) := by
  apply circularPeirceBasis.ext
  intro i
  simp only [Module.End.mul_apply, chiralParity_basis, map_smul,
    chiralParity_basis]
  fin_cases i <;> norm_num [parityWeight]

/-- Parity of a generator label: plus labels have `+1`, minus labels `-1`. -/
def generatorParity (g : ChiralGenerator) : ℝ :=
  parityWeight (generatorIndex g)

@[simp] theorem generatorParity_pPlus : generatorParity .pPlus = 1 := rfl
@[simp] theorem generatorParity_pMinus : generatorParity .pMinus = -1 := rfl

@[simp] theorem generatorParity_sPlus (i : Fin 3) :
    generatorParity (.sPlus i) = 1 := by
  fin_cases i <;> rfl

@[simp] theorem generatorParity_sMinus (i : Fin 3) :
    generatorParity (.sMinus i) = -1 := by
  fin_cases i <;> rfl

/-- Chiral generator states are simultaneous parity and axial-grading eigenstates. -/
theorem generatorState_joint_eigen (g : ChiralGenerator) :
    chiralParity (generatorState g) = generatorParity g • generatorState g ∧
    axialGrading (generatorState g) = (generatorDegree g : ℝ) • generatorState g := by
  constructor
  · exact chiralParity_basis (generatorIndex g)
  · exact generatorState_axial_eigen g

/-- Genuine circular operator lift of the free associative chiral envelope. -/
noncomputable def genuineChiralEnvelopeRepresentation :
    ChiralOperatorEnvelope ℝ →ₐ[ℝ] Module.End ℝ CZ :=
  FreeAlgebra.lift ℝ (fun g => leftMultiplication (generatorState g))

@[simp] theorem genuineChiralEnvelopeRepresentation_generator
    (g : ChiralGenerator) :
    genuineChiralEnvelopeRepresentation (ofGenerator (R := ℝ) g) =
      leftMultiplication (generatorState g) := by
  exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem genuineChiralEnvelopeRepresentation_PPlus :
    genuineChiralEnvelopeRepresentation (PPlus (R := ℝ)) = chiralPPlus := by
  rw [genuineChiralEnvelopeRepresentation_generator]
  simp [generatorState_pPlus, chiralPPlus]

@[simp] theorem genuineChiralEnvelopeRepresentation_PMinus :
    genuineChiralEnvelopeRepresentation (PMinus (R := ℝ)) = chiralPMinus := by
  rw [genuineChiralEnvelopeRepresentation_generator]
  simp [generatorState_pMinus, chiralPMinus]

@[simp] theorem genuineChiralEnvelopeRepresentation_SPlus (i : Fin 3) :
    genuineChiralEnvelopeRepresentation (SPlus (R := ℝ) i) =
      leftMultiplication (rootPlus i) := by
  rw [genuineChiralEnvelopeRepresentation_generator, generatorState_sPlus]

@[simp] theorem genuineChiralEnvelopeRepresentation_SMinus (i : Fin 3) :
    genuineChiralEnvelopeRepresentation (SMinus (R := ℝ) i) =
      leftMultiplication (rootMinus i) := by
  rw [genuineChiralEnvelopeRepresentation_generator, generatorState_sMinus]

end InfoGeometry.Lie.SplitOctonionChiralCircularSpectralBridge
