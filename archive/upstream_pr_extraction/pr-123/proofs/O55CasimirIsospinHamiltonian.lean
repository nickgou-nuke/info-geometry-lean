import proofs.SO55NullSU5KleinSpectral
import proofs.O55GradedGeneratorBasis
import proofs.CasimirIsospinHamiltonian

noncomputable section

namespace O55CasimirIsospinHamiltonian

abbrev Q := ℚ

def totalGenerators : Q := SO55NullSU5KleinSpectral.so55NullBlock_dim
def su5AdjointGenerators : Q := SO55NullSU5KleinSpectral.su5Adjoint_dim
def dilatonGenerators : Q := SO55NullSU5KleinSpectral.dilaton_dim
def activeGenerators : Q := O55GradedGeneratorBasis.activeGradedGeneratorCount
def spinEvenGenerators : Q := SO55NullSU5KleinSpectral.spinEven16_dim
def spinOddGenerators : Q := SO55NullSU5KleinSpectral.spinOdd16_dim
def spinTotalGenerators : Q := SO55NullSU5KleinSpectral.varlamovModePartition_dim

def activeO55Weight : Q := activeGenerators / totalGenerators
def dilatonSU5Weight : Q := dilatonGenerators / su5AdjointGenerators
def semispinorWeight : Q := spinEvenGenerators / spinTotalGenerators
def semispinorParityWeight : Q := (spinEvenGenerators - spinOddGenerators) / spinTotalGenerators

def structuralBreakingSign (s : ℤ) : Prop :=
  s = -1 ∨ s = 0 ∨ s = 1

def structuralIMME_b (s : ℤ) : Q :=
  (s : Q) * activeO55Weight

def structuralIMME_c : Q :=
  dilatonSU5Weight

def structuralPairT0 : Q :=
  semispinorWeight + activeO55Weight / 2

def structuralPairT1 : Q :=
  semispinorWeight - activeO55Weight / 2

def structuralSpring (m2 : Q) : Q :=
  CasimirIsospinHamiltonian.casimirStiffness
    (CasimirIsospinHamiltonian.massCasimir m2)

def o55StructuralHamiltonian
    (s : ℤ) (m2 J T v Tz : Q) : Q :=
  CasimirIsospinHamiltonian.generalizedHamiltonian
    1 activeO55Weight semispinorWeight dilatonSU5Weight
    0 (structuralIMME_b s) structuralIMME_c
    structuralPairT0 structuralPairT1 (structuralSpring m2)
    m2 J T v Tz

theorem total_generators_eq : totalGenerators = 45 := by
  norm_num [totalGenerators, SO55NullSU5KleinSpectral.so55NullBlock_dim,
    SO55NullSU5KleinSpectral.diagonalA_dim,
    SO55NullSU5KleinSpectral.matrixDim,
    SO55NullSU5KleinSpectral.n5,
    SO55NullSU5KleinSpectral.Bskew_dim,
    SO55NullSU5KleinSpectral.Cskew_dim,
    SO55NullSU5KleinSpectral.skewDim]

theorem su5_adjoint_generators_eq : su5AdjointGenerators = 24 := by
  norm_num [su5AdjointGenerators, SO55NullSU5KleinSpectral.sl5_dimension_24]

theorem dilaton_generators_eq : dilatonGenerators = 1 := by
  norm_num [dilatonGenerators, SO55NullSU5KleinSpectral.dilaton_dim,
    SO55NullSU5KleinSpectral.traceLineDim]

theorem active_generators_eq : activeGenerators = 15 := by
  norm_num [activeGenerators,
    O55GradedGeneratorBasis.activeGradedGeneratorCount,
    O55GradedGeneratorBasis.activeCompactGeneratorCount,
    O55GradedGeneratorBasis.activeMixedBoostCount,
    O55GradedGeneratorBasis.activePositiveCoordinates,
    O55GradedGeneratorBasis.activeNegativeCoordinates,
    O55GradedGeneratorBasis.chooseTwo]

theorem spin_even_generators_eq : spinEvenGenerators = 16 := by
  norm_num [spinEvenGenerators, SO55NullSU5KleinSpectral.spin_even_decomposition_16]

theorem spin_odd_generators_eq : spinOddGenerators = 16 := by
  norm_num [spinOddGenerators, SO55NullSU5KleinSpectral.spin_odd_decomposition_16]

theorem spin_total_generators_eq : spinTotalGenerators = 32 := by
  norm_num [spinTotalGenerators, SO55NullSU5KleinSpectral.varlamov_spin_mode_partition_32]

theorem active_o55_weight_eq : activeO55Weight = 1 / 3 := by
  norm_num [activeO55Weight, active_generators_eq, total_generators_eq]

theorem dilaton_su5_weight_eq : dilatonSU5Weight = 1 / 24 := by
  norm_num [dilatonSU5Weight, dilaton_generators_eq, su5_adjoint_generators_eq]

theorem semispinor_weight_eq : semispinorWeight = 1 / 2 := by
  norm_num [semispinorWeight, spin_even_generators_eq, spin_total_generators_eq]

theorem semispinor_parity_weight_eq : semispinorParityWeight = 0 := by
  norm_num [semispinorParityWeight, spin_even_generators_eq, spin_odd_generators_eq,
    spin_total_generators_eq]

theorem structural_pair_t0_eq : structuralPairT0 = 2 / 3 := by
  norm_num [structuralPairT0, semispinor_weight_eq, active_o55_weight_eq]

theorem structural_pair_t1_eq : structuralPairT1 = 1 / 3 := by
  norm_num [structuralPairT1, semispinor_weight_eq, active_o55_weight_eq]

theorem structural_pair_sum_eq : structuralPairT0 + structuralPairT1 = 1 := by
  norm_num [structural_pair_t0_eq, structural_pair_t1_eq]

theorem structural_pair_t1_lt_t0 : structuralPairT1 < structuralPairT0 := by
  norm_num [structural_pair_t0_eq, structural_pair_t1_eq]

theorem structural_imme_b_neg_eq : structuralIMME_b (-1) = -1 / 3 := by
  norm_num [structuralIMME_b, active_o55_weight_eq]

theorem structural_imme_b_zero_eq : structuralIMME_b 0 = 0 := by
  norm_num [structuralIMME_b, active_o55_weight_eq]

theorem structural_imme_b_pos_eq : structuralIMME_b 1 = 1 / 3 := by
  norm_num [structuralIMME_b, active_o55_weight_eq]

theorem structural_imme_c_eq : structuralIMME_c = 1 / 24 := by
  norm_num [structuralIMME_c, dilaton_su5_weight_eq]

theorem structural_spring_from_mass_casimir (m2 : Q) :
    structuralSpring m2 = m2 := by
  simp [structuralSpring, CasimirIsospinHamiltonian.mass_casimir_stiffness]

theorem o55_structural_mirror_difference (s : ℤ) (m2 J T v t : Q) :
    CasimirIsospinHamiltonian.mirrorDifference
      (fun Tz => o55StructuralHamiltonian s m2 J T v Tz) t =
      2 * ((s : Q) * (1 / 3)) * t := by
  unfold o55StructuralHamiltonian
  rw [CasimirIsospinHamiltonian.generalized_hamiltonian_mirror_difference]
  norm_num [structuralIMME_b, activeO55Weight, activeGenerators, totalGenerators,
    O55GradedGeneratorBasis.activeGradedGeneratorCount,
    O55GradedGeneratorBasis.activeCompactGeneratorCount,
    O55GradedGeneratorBasis.activeMixedBoostCount,
    O55GradedGeneratorBasis.activePositiveCoordinates,
    O55GradedGeneratorBasis.activeNegativeCoordinates,
    O55GradedGeneratorBasis.chooseTwo,
    SO55NullSU5KleinSpectral.so55NullBlock_dim,
    SO55NullSU5KleinSpectral.diagonalA_dim,
    SO55NullSU5KleinSpectral.matrixDim,
    SO55NullSU5KleinSpectral.n5,
    SO55NullSU5KleinSpectral.Bskew_dim,
    SO55NullSU5KleinSpectral.Cskew_dim,
    SO55NullSU5KleinSpectral.skewDim]

theorem o55_structural_mirror_symmetric (m2 J T v t : Q) :
    CasimirIsospinHamiltonian.mirrorDifference
      (fun Tz => o55StructuralHamiltonian 0 m2 J T v Tz) t = 0 := by
  simpa using o55_structural_mirror_difference 0 m2 J T v t

theorem o55_structural_mirror_oriented_positive (m2 J T v t : Q) :
    CasimirIsospinHamiltonian.mirrorDifference
      (fun Tz => o55StructuralHamiltonian 1 m2 J T v Tz) t =
      (2 / 3) * t := by
  simpa using o55_structural_mirror_difference 1 m2 J T v t

end O55CasimirIsospinHamiltonian

end noncomputable section
