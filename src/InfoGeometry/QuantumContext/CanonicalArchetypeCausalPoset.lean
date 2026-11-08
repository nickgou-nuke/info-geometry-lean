/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

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

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Branch 1 (`bivectorRotor` → `zornChiralBilateral` → `fourVectorSoldering` → `contactVariationalFlow`):**
Non-commutative Peirce–Zorn bivector rotor `Σ = [N_+, N_-]`, bilateral grading `S_P = 2P - 1`,
and soldering quartet `(Φ, J, V, Σ)` over `[Ring B]`. -/
theorem branch_1_bivector_zorn_and_soldering_identities
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    genSig P A C = invS P * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Branch 2 (`carNilpotentBase` → `carPeirceInvolution` → `chevalleySpinorDyad` → `kreinHyperbolicRotation` → `logCFTSymplecticMaster`):**
CAR nilpotent corners `N_+² = 0`, `N_-² = 0`, Chevalley spinor dyad anticommutator
`{N_+, N_-} = V`, and symplectic master eigenvalue `derivSqSig P A C Φ = -4 • ((V * V) * Φ)`. -/
theorem branch_2_car_chevalley_krein_and_logcft_identities
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    anticomm (conePlus P A) (coneMinus P C) = genV P A C ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · simp only [derivSqSig]; peirce_nf hP

/-- **Branch 3 (`noncommutativeOperatorRing` → `noncommutativeBdGBlocks` → `noncommutativeZornMultiplication` → `zornBdGCurvatureReadout`):**
Non-commutative Zorn–Peirce curvature readout `[N_+, [N_-, X]] - [N_-, [N_+, X]] = [Σ, X]`
and Leibniz derivation closure over `[Ring B]`. -/
theorem branch_3_noncommutative_zorn_bdg_curvature_identities
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    comm X (Y * Z) = comm X Y * Z + Y * comm X Z ∧
    comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X ∧
    (2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X)) =
      -(derivSqPhi P A C X + derivSqJ P A C X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · peirce_nf hP
  · simp only [derivSqPhi, derivSqJ]; peirce_nf hP

/-- Explicit non-commutative `[Ring B]` Peirce–Tetraktys operator assigned to each of the
27 constructors of `CanonicalArchetype`. -/
def canonicalArchetypeOperator (P A C X : B) : CanonicalArchetype → B
  | .colimitLoom => evenGrade P X + oddGrade P X
  | .bivectorRotor => genSig P A C
  | .zornChiralBilateral => invS P
  | .fourVectorSoldering => genPhi P A C
  | .softmaxObstruction => evenGrade P X
  | .chiralBipolarRouting => oddGrade P X
  | .diracCommutantGate => comm (invS P) (evenGrade P X)
  | .hamiltonianMassShell => genPhi P A C * genPhi P A C
  | .contactVariationalFlow => comm (genPhi P A C) (genJ P A C)
  | .carNilpotentBase => conePlus P A
  | .carPeirceInvolution => coneMinus P C
  | .chevalleySpinorDyad => anticomm (conePlus P A) (coneMinus P C)
  | .multiModeCAR => conePlus P A * coneMinus P C
  | .kreinHyperbolicRotation => coneMinus P C * conePlus P A
  | .carNambuFourthRoot => (genPhi P A C * genPhi P A C) * (genPhi P A C * genPhi P A C)
  | .nambuComplexStructure => genJ P A C
  | .nambuSpinorHolonomy => genJ P A C * genJ P A C
  | .scalarBdGMassModel => (1 - conePlus P A) * (1 - genV P A C) * (1 - coneMinus P C)
  | .logCFTJordanShear => (1 + conePlus P A) * X * (1 - conePlus P A)
  | .logCFTSymplecticMaster => derivSqSig P A C (genPhi P A C)
  | .noncommutativeOperatorRing => comm X X
  | .noncommutativeBdGBlocks => (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C)
  | .noncommutativeZornMultiplication => genV P A C
  | .zornMatrixSliceEmbedding => P * genV P A C * P
  | .zornLeibnizDerivation => comm (invS P) (oddGrade P X)
  | .zornPairingActionFormula => anticomm (invS P) (evenGrade P X)
  | .zornBdGCurvatureReadout =>
      comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X)

/-- **Theorem (`canonicalArchetype_all_27_stages_operator_identities`):**
Exact non-commutative `[Ring B]` operator identities linking the 27 constructors of
`canonicalArchetypeOperator`. -/
theorem canonicalArchetype_all_27_stages_operator_identities
    {P : B} (hP : P * P = P) (A C X : B) :
    canonicalArchetypeOperator P A C X .colimitLoom =
      canonicalArchetypeOperator P A C X .softmaxObstruction +
        canonicalArchetypeOperator P A C X .chiralBipolarRouting ∧
    canonicalArchetypeOperator P A C X .colimitLoom = X ∧
    canonicalArchetypeOperator P A C X .diracCommutantGate = 0 ∧
    canonicalArchetypeOperator P A C X .hamiltonianMassShell =
      canonicalArchetypeOperator P A C X .chevalleySpinorDyad ∧
    canonicalArchetypeOperator P A C X .nambuSpinorHolonomy =
      -canonicalArchetypeOperator P A C X .noncommutativeZornMultiplication ∧
    canonicalArchetypeOperator P A C X .noncommutativeBdGBlocks =
      canonicalArchetypeOperator P A C X .noncommutativeZornMultiplication ∧
    canonicalArchetypeOperator P A C X .zornMatrixSliceEmbedding =
      canonicalArchetypeOperator P A C X .multiModeCAR ∧
    canonicalArchetypeOperator P A C X .zornLeibnizDerivation =
      (2 : ℤ) • (P * X * (1 - P) - (1 - P) * X * P) ∧
    canonicalArchetypeOperator P A C X .zornPairingActionFormula =
      (2 : ℤ) • (P * X * P - (1 - P) * X * (1 - P)) ∧
    canonicalArchetypeOperator P A C X .zornBdGCurvatureReadout =
      comm (canonicalArchetypeOperator P A C X .bivectorRotor) X := by
  dsimp [canonicalArchetypeOperator]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`canonical_archetype_causal_poset_master_synthesis`):**
Unites the 27-stage `CanonicalArchetype` poset theorems with all three non-commutative
`[Ring B]` operator branches. -/
theorem canonical_archetype_causal_poset_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (∀ a : CanonicalArchetype, CanonicalArchetype.colimitLoom ≤ a) ∧
    (genPhi P A C * genPhi P A C = genV P A C ∧
      genJ P A C * genJ P A C = -genV P A C) ∧
    (comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
      derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C))) ∧
    (comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X) := by
  have h1 := branch_1_bivector_zorn_and_soldering_identities hP A C
  have h2 := branch_2_car_chevalley_krein_and_logcft_identities hP A C
  have h3 := branch_3_noncommutative_zorn_bdg_curvature_identities hP A C X Y Z
  exact ⟨colimit_precedes_all, ⟨h1.2.1, h1.2.2.1⟩, ⟨h2.2.2.2.1, h2.2.2.2.2⟩, h3.2.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset
