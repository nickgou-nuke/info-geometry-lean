import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# A Finite Poset of Repository Archetype Labels

This module equips a finite collection of repository archetype labels with the
partial order induced by inclusion of their explicitly assigned prerequisite
index sets. The results concern this encoding only; they do not establish
physical causation or prove the analytic, geometric, or dynamical claims
suggested by the labels.

The constructors are labels and `causalPrerequisites` is the data defining
their order. No physical model is defined here. In particular,
`hamiltonianMassShell` is only a label: this module contains no momentum,
metric, Hamiltonian, or dispersion relation. The CAR/Nambu labels record the
dependency structure of the separately proved operator identities; they do
not identify that branch with the scalar mass-shell label.

Zero debt, 0 sorry, 0 admit, kernel-verified in Lean 4.
-/

namespace InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset

/-- Twenty-seven labels used by this finite prerequisite-index encoding. -/
inductive CanonicalArchetype
  | colimitLoom
  | bivectorRotor
  | zornChiralBilateral
  | fourVectorSoldering
  | softmaxObstruction
  | chiralBipolarRouting
  | diracCommutantGate
  | hamiltonianMassShell
  | contactVariationalFlow
  | carNilpotentBase
  | carPeirceInvolution
  | chevalleySpinorDyad
  | multiModeCAR
  | kreinHyperbolicRotation
  | carNambuFourthRoot
  | nambuComplexStructure
  | nambuSpinorHolonomy
  | scalarBdGMassModel
  | logCFTJordanShear
  | logCFTSymplecticMaster
  | noncommutativeOperatorRing
  | noncommutativeBdGBlocks
  | noncommutativeZornMultiplication
  | zornMatrixSliceEmbedding
  | zornLeibnizDerivation
  | zornPairingActionFormula
  | zornBdGCurvatureReadout
  deriving DecidableEq

instance : Fintype CanonicalArchetype where
  elems := { .colimitLoom, .bivectorRotor, .zornChiralBilateral,
    .fourVectorSoldering, .softmaxObstruction, .chiralBipolarRouting,
    .diracCommutantGate, .hamiltonianMassShell, .contactVariationalFlow,
    .carNilpotentBase, .carPeirceInvolution, .chevalleySpinorDyad,
    .multiModeCAR, .kreinHyperbolicRotation, .carNambuFourthRoot,
    .nambuComplexStructure, .nambuSpinorHolonomy, .scalarBdGMassModel,
    .logCFTJordanShear, .logCFTSymplecticMaster,
    .noncommutativeOperatorRing, .noncommutativeBdGBlocks,
    .noncommutativeZornMultiplication, .zornMatrixSliceEmbedding,
    .zornLeibnizDerivation, .zornPairingActionFormula,
    .zornBdGCurvatureReadout }
  complete := by
    intro x
    cases x <;> simp

/-- Explicit prerequisite-index sets; inclusion, not physical causation, defines
the order used by this module. -/
def causalPrerequisites : CanonicalArchetype → Finset ℕ
  | .colimitLoom            => {0}
  | .bivectorRotor          => {0, 1}
  | .zornChiralBilateral    => {0, 1, 2}
  | .fourVectorSoldering    => {0, 1, 2, 3}
  | .softmaxObstruction     => {0, 1, 4}
  | .chiralBipolarRouting   => {0, 1, 4, 5}
  | .diracCommutantGate     => {0, 1, 4, 5, 6}
  | .hamiltonianMassShell   => {0, 1, 2, 3, 4, 5, 6, 7}
  | .contactVariationalFlow => {0, 1, 2, 3, 4, 5, 6, 7, 8}
  | .carNilpotentBase => {0, 9}
  | .carPeirceInvolution => {0, 9, 10}
  | .chevalleySpinorDyad => {0, 9, 10, 11}
  | .multiModeCAR => {0, 9, 10, 11, 12}
  | .kreinHyperbolicRotation => {0, 9, 10, 11, 12, 13}
  | .carNambuFourthRoot => {0, 9, 10, 11, 14}
  | .nambuComplexStructure => {0, 9, 10, 11, 14, 15}
  | .nambuSpinorHolonomy => {0, 9, 10, 11, 14, 15, 16}
  | .scalarBdGMassModel => {0, 9, 10, 11, 12, 13, 17}
  | .logCFTJordanShear => {0, 9, 10, 11, 25}
  | .logCFTSymplecticMaster => {0, 9, 10, 11, 14, 15, 16, 25, 26}
  | .noncommutativeOperatorRing => {0, 18}
  | .noncommutativeBdGBlocks => {0, 18, 19}
  | .noncommutativeZornMultiplication => {0, 18, 20}
  | .zornMatrixSliceEmbedding => {0, 18, 20, 21}
  | .zornLeibnizDerivation => {0, 18, 20, 22}
  | .zornPairingActionFormula => {0, 18, 20, 23}
  | .zornBdGCurvatureReadout => {0, 18, 19, 20, 21, 24}

/-- **Theorem 1 (Causal Prerequisites Faithfulness)**:
    The assignment of causal prerequisites is strictly injective. -/
theorem causalPrerequisites_injective : Function.Injective causalPrerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

/-- The canonical Partial Order structure on physical and mathematical archetypes. -/
instance : PartialOrder CanonicalArchetype :=
  PartialOrder.lift causalPrerequisites causalPrerequisites_injective

/-- Decidable ordering relation for automatic verification. -/
instance : DecidableRel (α := CanonicalArchetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (causalPrerequisites left ⊆ causalPrerequisites right))

/-- The `colimitLoom` index set is included in every encoded prerequisite set. -/
theorem colimit_precedes_all (a : CanonicalArchetype) :
    CanonicalArchetype.colimitLoom ≤ a := by
  cases a <;> decide

/-- Encoded prerequisite inclusion from the bivector label to the Zorn label. -/
theorem bivector_precedes_zorn :
    CanonicalArchetype.bivectorRotor ≤ CanonicalArchetype.zornChiralBilateral := by
  decide

/-- Encoded prerequisite inclusion from the Zorn label to the soldering label. -/
theorem zorn_precedes_soldering :
    CanonicalArchetype.zornChiralBilateral ≤ CanonicalArchetype.fourVectorSoldering := by
  decide

/-- Encoded prerequisite inclusion between the softmax and routing labels. -/
theorem obstruction_precedes_chiral_repair :
    CanonicalArchetype.softmaxObstruction ≤ CanonicalArchetype.chiralBipolarRouting := by
  decide

/-- Encoded prerequisite inclusion from the routing label to the commutant label. -/
theorem chiral_repair_enables_dirac_gate :
    CanonicalArchetype.chiralBipolarRouting ≤ CanonicalArchetype.diracCommutantGate := by
  decide

/-- Encoded prerequisite inclusion only; no mass-shell theorem is proved here. -/
theorem dirac_gate_enables_mass_shell :
    CanonicalArchetype.diracCommutantGate ≤ CanonicalArchetype.hamiltonianMassShell := by
  decide

/-- Encoded prerequisite inclusion only; no variational-flow consequence is proved here. -/
theorem mass_shell_enables_contact_flow :
    CanonicalArchetype.hamiltonianMassShell ≤ CanonicalArchetype.contactVariationalFlow := by
  decide

/-! The following order facts integrate the CAR/BdG synthesis and its Nambu
holonomy consequences into this shared prerequisite poset. -/

theorem car_base_precedes_peirce :
    CanonicalArchetype.carNilpotentBase ≤ CanonicalArchetype.carPeirceInvolution := by
  decide

theorem car_peirce_precedes_chevalley_dyad :
    CanonicalArchetype.carPeirceInvolution ≤ CanonicalArchetype.chevalleySpinorDyad := by
  decide

theorem chevalley_dyad_precedes_multimode_car :
    CanonicalArchetype.chevalleySpinorDyad ≤ CanonicalArchetype.multiModeCAR := by
  decide

theorem multimode_car_precedes_krein_rotation :
    CanonicalArchetype.multiModeCAR ≤ CanonicalArchetype.kreinHyperbolicRotation := by
  decide

theorem chevalley_dyad_precedes_car_nambu :
    CanonicalArchetype.chevalleySpinorDyad ≤ CanonicalArchetype.carNambuFourthRoot := by
  decide

theorem car_nambu_precedes_complex_structure :
    CanonicalArchetype.carNambuFourthRoot ≤ CanonicalArchetype.nambuComplexStructure := by
  decide

theorem complex_structure_precedes_spinor_holonomy :
    CanonicalArchetype.nambuComplexStructure ≤ CanonicalArchetype.nambuSpinorHolonomy := by
  decide

theorem krein_rotation_precedes_scalar_mass_model :
    CanonicalArchetype.kreinHyperbolicRotation ≤ CanonicalArchetype.scalarBdGMassModel := by
  decide

/-- The multi-mode/Krein path and the CAR/Nambu path are distinct branches in
the encoded prerequisite order; neither label is silently identified with the other. -/
theorem krein_and_car_nambu_branches_incomparable :
    ¬ CanonicalArchetype.kreinHyperbolicRotation ≤ CanonicalArchetype.carNambuFourthRoot ∧
      ¬ CanonicalArchetype.carNambuFourthRoot ≤ CanonicalArchetype.kreinHyperbolicRotation := by
  decide

/-! ### LogCFT Jordan shear and symplectic master stages -/

theorem chevalley_dyad_precedes_logcft_shear :
    CanonicalArchetype.chevalleySpinorDyad ≤ CanonicalArchetype.logCFTJordanShear := by
  decide

theorem spinor_holonomy_precedes_logcft_master :
    CanonicalArchetype.nambuSpinorHolonomy ≤ CanonicalArchetype.logCFTSymplecticMaster := by
  decide

theorem logcft_shear_precedes_logcft_master :
    CanonicalArchetype.logCFTJordanShear ≤ CanonicalArchetype.logCFTSymplecticMaster := by
  decide

theorem logcft_shear_and_spinor_holonomy_incomparable :
    ¬ CanonicalArchetype.logCFTJordanShear ≤ CanonicalArchetype.nambuSpinorHolonomy ∧
      ¬ CanonicalArchetype.nambuSpinorHolonomy ≤ CanonicalArchetype.logCFTJordanShear := by
  decide

theorem logcft_shear_and_zorn_incomparable :
    ¬ CanonicalArchetype.logCFTJordanShear ≤ CanonicalArchetype.zornBdGCurvatureReadout ∧
      ¬ CanonicalArchetype.zornBdGCurvatureReadout ≤ CanonicalArchetype.logCFTJordanShear := by
  decide

/-! The noncommutative Zorn lane is added as a separate branch. Its curvature
readout depends on both the matrix BdG calculation and the proved matrix-to-Zorn
multiplicative embedding. The displayed pairing formula is kept separate from
the Leibniz-derivation structure because the current owner proves no map
identifying those two objects. -/

theorem noncommutative_ring_precedes_bdg_blocks :
    CanonicalArchetype.noncommutativeOperatorRing ≤
      CanonicalArchetype.noncommutativeBdGBlocks := by
  decide

theorem noncommutative_ring_precedes_zorn_multiplication :
    CanonicalArchetype.noncommutativeOperatorRing ≤
      CanonicalArchetype.noncommutativeZornMultiplication := by
  decide

theorem zorn_multiplication_precedes_matrix_slice :
    CanonicalArchetype.noncommutativeZornMultiplication ≤
      CanonicalArchetype.zornMatrixSliceEmbedding := by
  decide

theorem zorn_multiplication_precedes_leibniz_derivation :
    CanonicalArchetype.noncommutativeZornMultiplication ≤
      CanonicalArchetype.zornLeibnizDerivation := by
  decide

theorem zorn_multiplication_precedes_pairing_formula :
    CanonicalArchetype.noncommutativeZornMultiplication ≤
      CanonicalArchetype.zornPairingActionFormula := by
  decide

theorem bdg_blocks_precede_zorn_curvature_readout :
    CanonicalArchetype.noncommutativeBdGBlocks ≤
      CanonicalArchetype.zornBdGCurvatureReadout := by
  decide

theorem zorn_matrix_slice_precedes_curvature_readout :
    CanonicalArchetype.zornMatrixSliceEmbedding ≤
      CanonicalArchetype.zornBdGCurvatureReadout := by
  decide

/-- The owner has a Leibniz derivation structure and a separate pairing-action
formula, but no theorem identifying the latter as an instance of the former. -/
theorem zorn_derivation_and_pairing_formula_incomparable :
    ¬ CanonicalArchetype.zornLeibnizDerivation ≤
        CanonicalArchetype.zornPairingActionFormula ∧
      ¬ CanonicalArchetype.zornPairingActionFormula ≤
        CanonicalArchetype.zornLeibnizDerivation := by
  decide

/-- **Theorem 9 (Incomparability of Independent Branches)**:
    The purely algebraic 4-vector soldering and the softmax obstruction are mutually independent
    branches diverging from the bivector rotor stage. -/
theorem soldering_and_obstruction_incomparable :
    ¬ CanonicalArchetype.fourVectorSoldering ≤ CanonicalArchetype.softmaxObstruction ∧
      ¬ CanonicalArchetype.softmaxObstruction ≤ CanonicalArchetype.fourVectorSoldering := by
  decide

/-- **Theorem 10 (Strict Causal Poset Acyclicity)**:
    No feedback cycles exist in the causal ordering of physical and mathematical archetypes:
    $$\forall a, b, \quad a \le b \land b \le a \implies a = b$$ -/
theorem causal_poset_acyclic (left right : CanonicalArchetype)
    (forward : left ≤ right) (backward : right ≤ left) : left = right :=
  le_antisymm forward backward

end InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset
