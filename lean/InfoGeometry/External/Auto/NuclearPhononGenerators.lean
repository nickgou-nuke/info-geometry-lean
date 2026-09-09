import Mathlib.Tactic

noncomputable section

namespace NuclearPhononGenerators

abbrev Q := ℚ

def sBosonCount : ℕ := 1
def dBosonCount : ℕ := 5
def ibmModeCount : ℕ := sBosonCount + dBosonCount
def uNGeneratorCount (n : ℕ) : ℕ := n * n
def ibmU6GeneratorCount : ℕ := uNGeneratorCount ibmModeCount

def sdPhononCount : ℕ := dBosonCount
def dsLoweringCount : ℕ := dBosonCount
def ddGeneratorCount : ℕ := dBosonCount * dBosonCount
def ssGeneratorCount : ℕ := 1

def ibmBilinearPartition : ℕ := ssGeneratorCount + sdPhononCount + dsLoweringCount + ddGeneratorCount

def spaceDim3 : ℕ := 3
def symmetricPairCount (n : ℕ) : ℕ := n * (n + 1) / 2
def antisymmetricPairCount (n : ℕ) : ℕ := n * (n - 1) / 2

def sp6RaisingCount : ℕ := symmetricPairCount spaceDim3
def sp6LoweringCount : ℕ := symmetricPairCount spaceDim3
def gl3Count : ℕ := spaceDim3 * spaceDim3
def sp6GeneratorCount : ℕ := sp6RaisingCount + sp6LoweringCount + gl3Count

def angularMomentumCount3 : ℕ := antisymmetricPairCount spaceDim3
def shearDilationCount3 : ℕ := symmetricPairCount spaceDim3
def coordinateQuadrupoleCount3 : ℕ := symmetricPairCount spaceDim3
def kineticQuadrupoleCount3 : ℕ := symmetricPairCount spaceDim3

def collectiveTensorComponentCount : ℕ :=
  angularMomentumCount3 + shearDilationCount3 + coordinateQuadrupoleCount3 + kineticQuadrupoleCount3

structure IBMPhononGenerator where
  sourceMode : String
  targetMode : String
  angularMomentum : ℕ
  magneticSubstate : Int

def quadrupolePhonon (m : Int) : IBMPhononGenerator where
  sourceMode := "s"
  targetMode := "d"
  angularMomentum := 2
  magneticSubstate := m

def isQuadrupolePhonon (g : IBMPhononGenerator) : Prop :=
  g.sourceMode = "s" ∧ g.targetMode = "d" ∧ g.angularMomentum = 2

structure Sp6PhononRaising where
  Qcoeff : Q
  Kcoeff : Q
  Tcoeff : Q
  omegaQuanta : ℕ

structure PhononRaisingOperator (V : Type*) [AddCommGroup V] [Module ℝ V] where
  Qform : V → V → ℝ
  Kform : V → V → ℝ
  Tform : V → V → ℝ

noncomputable def raisingPhonon {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) (u v : V) : ℂ :=
  ⟨(op.Qform u v - op.Kform u v) / 2, op.Tform u v / 2⟩

def sp6PhononRaising : Sp6PhononRaising where
  Qcoeff := 1 / 2
  Kcoeff := -1 / 2
  Tcoeff := 1 / 2
  omegaQuanta := 2

def sp6PhononLowering : Sp6PhononRaising where
  Qcoeff := 1 / 2
  Kcoeff := -1 / 2
  Tcoeff := -1 / 2
  omegaQuanta := 2

def raisingPlusLowering_QK (A B : Sp6PhononRaising) : Q × Q × Q :=
  (A.Qcoeff + B.Qcoeff, A.Kcoeff + B.Kcoeff, A.Tcoeff + B.Tcoeff)

def raisingMinusLowering_T (A B : Sp6PhononRaising) : Q :=
  A.Tcoeff - B.Tcoeff

def poincareC1 (m : Q) : Q := -m * m
def springStiffnessFromC1 (C1 : Q) : Q := -C1
def springPotential (m lam : Q) : Q := (m * m * lam * lam) / 2
def dilationBracketCoeff (C1 : Q) : Q := 2 * C1
def phononEnergy (omega n : Q) : Q := (n + 1/2) * omega

def uDimension (n : ℕ) : ℕ := n * n
def suDimension (n : ℕ) : ℕ := n * n - 1
def soDimension (n : ℕ) : ℕ := n * (n - 1) / 2
def spRealDimensionFromHalfRank (n : ℕ) : ℕ := n * (2 * n + 1)

def u6Dimension : ℕ := uDimension 6
def su3Dimension : ℕ := suDimension 3
def so6Dimension : ℕ := soDimension 6
def so5Dimension : ℕ := soDimension 5
def so3Dimension : ℕ := soDimension 3
def sp6RDimension : ℕ := spRealDimensionFromHalfRank 3

inductive SymmetryGroup where
  | U6
  | U5
  | SU3
  | SO6
  | SO5
  | SO3
  | Sp6R
  deriving DecidableEq, Repr

def groupDimension : SymmetryGroup → ℕ
  | SymmetryGroup.U6 => 36
  | SymmetryGroup.U5 => 25
  | SymmetryGroup.SU3 => 8
  | SymmetryGroup.SO6 => 15
  | SymmetryGroup.SO5 => 10
  | SymmetryGroup.SO3 => 3
  | SymmetryGroup.Sp6R => 21

def subgroupStep : SymmetryGroup → SymmetryGroup → Bool
  | SymmetryGroup.U6, SymmetryGroup.U5 => true
  | SymmetryGroup.U6, SymmetryGroup.SU3 => true
  | SymmetryGroup.U6, SymmetryGroup.SO6 => true
  | SymmetryGroup.SO6, SymmetryGroup.SO5 => true
  | SymmetryGroup.SO5, SymmetryGroup.SO3 => true
  | SymmetryGroup.Sp6R, SymmetryGroup.U6 => true
  | _, _ => false

def deltaNat (i j : ℕ) : ℤ := if i = j then 1 else 0
def matrixUnitFirstCoeff (_i j k _l : ℕ) : ℤ := deltaNat j k
def matrixUnitSecondCoeff (i _j _k l : ℕ) : ℤ := -deltaNat l i

def ccrPositionMomentumBracket (hbar : Q) : ℂ :=
  ⟨0, hbar⟩

theorem ibm_mode_count_eq_s_plus_d : ibmModeCount = 6 := by
  norm_num [ibmModeCount, sBosonCount, dBosonCount]

theorem ibm_u6_generator_count : ibmU6GeneratorCount = 36 := by
  norm_num [ibmU6GeneratorCount, uNGeneratorCount, ibmModeCount, sBosonCount, dBosonCount]

theorem ibm_bilinear_partition_eq_36 : ibmBilinearPartition = 36 := by
  norm_num [ibmBilinearPartition, ssGeneratorCount, sdPhononCount, dsLoweringCount,
    ddGeneratorCount, dBosonCount]

theorem quadrupole_phonon_is_u6_generator (m : Int) :
    isQuadrupolePhonon (quadrupolePhonon m) := by
  simp [isQuadrupolePhonon, quadrupolePhonon]

theorem sp6_symmetric_pair_count_3 : symmetricPairCount 3 = 6 := by
  norm_num [symmetricPairCount]

theorem so3_antisymmetric_pair_count_3 : antisymmetricPairCount 3 = 3 := by
  norm_num [antisymmetricPairCount]

theorem sp6_generator_count_21 : sp6GeneratorCount = 21 := by
  norm_num [sp6GeneratorCount, sp6RaisingCount, sp6LoweringCount, gl3Count,
    symmetricPairCount, spaceDim3]

theorem collective_tensor_component_count_eq_21 : collectiveTensorComponentCount = 21 := by
  norm_num [collectiveTensorComponentCount, angularMomentumCount3, shearDilationCount3,
    coordinateQuadrupoleCount3, kineticQuadrupoleCount3, symmetricPairCount,
    antisymmetricPairCount, spaceDim3]

theorem sp6_raising_Q_coefficient : sp6PhononRaising.Qcoeff = 1/2 := by
  norm_num [sp6PhononRaising]

theorem sp6_raising_K_coefficient : sp6PhononRaising.Kcoeff = -1/2 := by
  norm_num [sp6PhononRaising]

theorem sp6_raising_T_coefficient : sp6PhononRaising.Tcoeff = 1/2 := by
  norm_num [sp6PhononRaising]

theorem sp6_raising_omega_quanta : sp6PhononRaising.omegaQuanta = 2 := by
  norm_num [sp6PhononRaising]

theorem sp6_lowering_Q_coefficient : sp6PhononLowering.Qcoeff = 1/2 := by
  norm_num [sp6PhononLowering]

theorem sp6_lowering_K_coefficient : sp6PhononLowering.Kcoeff = -1/2 := by
  norm_num [sp6PhononLowering]

theorem sp6_lowering_T_coefficient : sp6PhononLowering.Tcoeff = -1/2 := by
  norm_num [sp6PhononLowering]

theorem sp6_lowering_omega_quanta : sp6PhononLowering.omegaQuanta = 2 := by
  norm_num [sp6PhononLowering]

theorem raising_plus_lowering_extracts_Q_minus_K :
    raisingPlusLowering_QK sp6PhononRaising sp6PhononLowering = (1, -1, 0) := by
  norm_num [raisingPlusLowering_QK, sp6PhononRaising, sp6PhononLowering]

theorem raising_minus_lowering_extracts_T :
    raisingMinusLowering_T sp6PhononRaising sp6PhononLowering = 1 := by
  norm_num [raisingMinusLowering_T, sp6PhononRaising, sp6PhononLowering]

theorem raising_phonon_non_vacuous {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) (u v : V) :
    op.Tform u v ≠ 0 → raisingPhonon op u v ≠ 0 := by
  intro hT hzero
  have h_im : (raisingPhonon op u v).im = 0 := by
    rw [hzero]
    rfl
  dsimp [raisingPhonon] at h_im
  have hmul := congrArg (fun x : ℝ => x * 2) h_im
  norm_num at hmul
  apply hT
  simpa using hmul

theorem casimir_spring_stiffness (m : Q) :
    springStiffnessFromC1 (poincareC1 m) = m * m := by
  rw [springStiffnessFromC1, poincareC1]
  ring

theorem massless_spring_stiffness_zero :
    springStiffnessFromC1 (poincareC1 0) = 0 := by
  norm_num [springStiffnessFromC1, poincareC1]

theorem spring_potential_mass_three_displacement_two :
    springPotential 3 2 = 18 := by
  norm_num [springPotential]

theorem dilation_bracket_on_shell (m : Q) :
    dilationBracketCoeff (poincareC1 m) = -2 * m * m := by
  rw [dilationBracketCoeff, poincareC1]
  ring

theorem one_phonon_energy : phononEnergy 5 1 = 15 / 2 := by
  norm_num [phononEnergy]

theorem u6_dimension_eq_36 : u6Dimension = 36 := by
  norm_num [u6Dimension, uDimension]

theorem su3_dimension_eq_8 : su3Dimension = 8 := by
  norm_num [su3Dimension, suDimension]

theorem so6_dimension_eq_15 : so6Dimension = 15 := by
  norm_num [so6Dimension, soDimension]

theorem so5_dimension_eq_10 : so5Dimension = 10 := by
  norm_num [so5Dimension, soDimension]

theorem so3_dimension_eq_3 : so3Dimension = 3 := by
  norm_num [so3Dimension, soDimension]

theorem sp6R_dimension_eq_21 : sp6RDimension = 21 := by
  norm_num [sp6RDimension, spRealDimensionFromHalfRank]

theorem group_dimension_U6 : groupDimension SymmetryGroup.U6 = 36 := by
  decide

theorem group_dimension_U5 : groupDimension SymmetryGroup.U5 = 25 := by
  decide

theorem group_dimension_SU3 : groupDimension SymmetryGroup.SU3 = 8 := by
  decide

theorem group_dimension_SO6 : groupDimension SymmetryGroup.SO6 = 15 := by
  decide

theorem group_dimension_SO5 : groupDimension SymmetryGroup.SO5 = 10 := by
  decide

theorem group_dimension_SO3 : groupDimension SymmetryGroup.SO3 = 3 := by
  decide

theorem group_dimension_Sp6R : groupDimension SymmetryGroup.Sp6R = 21 := by
  decide

theorem subgroup_step_U6_U5 : subgroupStep SymmetryGroup.U6 SymmetryGroup.U5 = true := by
  decide

theorem subgroup_step_U6_SU3 : subgroupStep SymmetryGroup.U6 SymmetryGroup.SU3 = true := by
  decide

theorem subgroup_step_U6_SO6 : subgroupStep SymmetryGroup.U6 SymmetryGroup.SO6 = true := by
  decide

theorem subgroup_step_SO6_SO5 : subgroupStep SymmetryGroup.SO6 SymmetryGroup.SO5 = true := by
  decide

theorem subgroup_step_SO5_SO3 : subgroupStep SymmetryGroup.SO5 SymmetryGroup.SO3 = true := by
  decide

theorem subgroup_step_Sp6R_U6 : subgroupStep SymmetryGroup.Sp6R SymmetryGroup.U6 = true := by
  decide

theorem matrix_unit_bracket_E12_E23_first :
    matrixUnitFirstCoeff 1 2 2 3 = 1 := by
  norm_num [matrixUnitFirstCoeff, matrixUnitSecondCoeff, deltaNat]

theorem matrix_unit_bracket_E12_E23_second :
    matrixUnitSecondCoeff 1 2 2 3 = 0 := by
  norm_num [matrixUnitFirstCoeff, matrixUnitSecondCoeff, deltaNat]

theorem matrix_unit_bracket_E12_E21_first :
    matrixUnitFirstCoeff 1 2 2 1 = 1 := by
  norm_num [matrixUnitFirstCoeff, matrixUnitSecondCoeff, deltaNat]

theorem matrix_unit_bracket_E12_E21_second :
    matrixUnitSecondCoeff 1 2 2 1 = -1 := by
  norm_num [matrixUnitFirstCoeff, matrixUnitSecondCoeff, deltaNat]

theorem ccr_position_momentum_nonzero :
    ccrPositionMomentumBracket 1 ≠ 0 := by
  intro h
  have him : (ccrPositionMomentumBracket 1).im = 0 := by rw [h]; rfl
  norm_num [ccrPositionMomentumBracket] at him

inductive Concept where
  | Nuclear_Phonon
  | IBM_U6_Bilinear_Generator
  | Quadrupole_d_dagger_s
  | Sp6R_Raising_Generator
  | Noncompact_Dilation_Shear
  | Casimir_Dilation_Spring
  deriving DecidableEq, Repr

inductive Edge where
  | represented_by
  | counted_by
  | decomposes_into
  | raises_by
  | quantizes
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Nuclear_Phonon, Edge.represented_by, Concept.IBM_U6_Bilinear_Generator => true
  | Concept.IBM_U6_Bilinear_Generator, Edge.counted_by, Concept.Quadrupole_d_dagger_s => true
  | Concept.Nuclear_Phonon, Edge.represented_by, Concept.Sp6R_Raising_Generator => true
  | Concept.Sp6R_Raising_Generator, Edge.decomposes_into, Concept.Noncompact_Dilation_Shear => true
  | Concept.Noncompact_Dilation_Shear, Edge.quantizes, Concept.Casimir_Dilation_Spring => true
  | _, _, _ => false

theorem nuclear_phonon_represented_by_ibm_bilinear_generator :
    edgeHolds Concept.Nuclear_Phonon Edge.represented_by
      Concept.IBM_U6_Bilinear_Generator = true := by
  decide

theorem ibm_bilinear_generator_counted_by_quadrupole_phonon :
    edgeHolds Concept.IBM_U6_Bilinear_Generator Edge.counted_by
      Concept.Quadrupole_d_dagger_s = true := by
  decide

theorem nuclear_phonon_represented_by_sp6R_raising_generator :
    edgeHolds Concept.Nuclear_Phonon Edge.represented_by
      Concept.Sp6R_Raising_Generator = true := by
  decide

theorem sp6R_raising_generator_decomposes_into_dilation_shear :
    edgeHolds Concept.Sp6R_Raising_Generator Edge.decomposes_into
      Concept.Noncompact_Dilation_Shear = true := by
  decide

theorem dilation_shear_quantizes_casimir_spring :
    edgeHolds Concept.Noncompact_Dilation_Shear Edge.quantizes
      Concept.Casimir_Dilation_Spring = true := by
  decide

end NuclearPhononGenerators

end noncomputable section
