/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.DeriveFintype
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# The dependency partial order

The edges record the mathematical prerequisites of this development. Reachability,
not a chosen numbering, defines the order. The rank only proves acyclicity.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.DependencyPoset

inductive Archetype
  | operatorAlgebra
  | additiveBilinearity
  | peirceCorners
  | operatorTriples
  | jordanProduct
  | jordanGeometry
  | universalDefects
  | peirceGeometry
  | crossIdentities
  | zornProduct
  | zornCorners
  | channelAssociators
  | reflection
  | numberDefect
  | oddGeneration
  | evenAssociatorRange
  | jacobiatorResolution
  | reflectionCancellation
  | braidingDefect
  | expressionSyntax
  | expressionEvaluation
  | contextPropagation
  | rotationOrder
  | pathCorrection
  | signObstruction
  deriving DecidableEq, Repr

open Archetype

instance : Fintype Archetype where
  elems := {operatorAlgebra, additiveBilinearity, peirceCorners, operatorTriples,
    jordanProduct, jordanGeometry, universalDefects, peirceGeometry, crossIdentities, zornProduct,
    zornCorners, channelAssociators, reflection, numberDefect, oddGeneration,
    evenAssociatorRange, jacobiatorResolution,
    reflectionCancellation, braidingDefect, expressionSyntax, expressionEvaluation,
    contextPropagation, rotationOrder, pathCorrection, signObstruction}
  complete a := by cases a <;> simp

inductive Edge : Archetype → Archetype → Prop
  | operator_peirce : Edge operatorAlgebra peirceCorners
  | operator_triples : Edge operatorAlgebra operatorTriples
  | operator_jordan : Edge operatorAlgebra jordanProduct
  | jordan_geometry : Edge jordanProduct jordanGeometry
  | additive_defects : Edge additiveBilinearity universalDefects
  | peirce_geometry : Edge peirceCorners peirceGeometry
  | triples_cross : Edge operatorTriples crossIdentities
  | triples_zorn : Edge operatorTriples zornProduct
  | zorn_corners : Edge zornProduct zornCorners
  | zorn_associators : Edge zornProduct channelAssociators
  | zorn_reflection : Edge zornProduct reflection
  | zorn_number : Edge zornProduct numberDefect
  | zorn_generation : Edge zornProduct oddGeneration
  | cross_evenRange : Edge crossIdentities evenAssociatorRange
  | associators_evenRange : Edge channelAssociators evenAssociatorRange
  | corners_jacobiator : Edge zornCorners jacobiatorResolution
  | associators_jacobiator : Edge channelAssociators jacobiatorResolution
  | defects_jacobiator : Edge universalDefects jacobiatorResolution
  | cross_jacobiator : Edge crossIdentities jacobiatorResolution
  | cross_cancellation : Edge crossIdentities reflectionCancellation
  | associators_cancellation : Edge channelAssociators reflectionCancellation
  | reflection_cancellation : Edge reflection reflectionCancellation
  | cross_braiding : Edge crossIdentities braidingDefect
  | associators_braiding : Edge channelAssociators braidingDefect
  | operator_syntax : Edge operatorAlgebra expressionSyntax
  | syntax_evaluation : Edge expressionSyntax expressionEvaluation
  | zorn_evaluation : Edge zornProduct expressionEvaluation
  | syntax_order : Edge expressionSyntax rotationOrder
  | additive_context : Edge additiveBilinearity contextPropagation
  | evaluation_context : Edge expressionEvaluation contextPropagation
  | context_path : Edge contextPropagation pathCorrection
  | defects_path : Edge universalDefects pathCorrection
  | cancellation_path : Edge reflectionCancellation pathCorrection
  | braiding_sign : Edge braidingDefect signObstruction

def rank : Archetype → ℕ
  | operatorAlgebra | additiveBilinearity => 0
  | peirceCorners | operatorTriples | jordanProduct | universalDefects | expressionSyntax => 1
  | peirceGeometry | crossIdentities | zornProduct | jordanGeometry | rotationOrder => 2
  | zornCorners | channelAssociators | reflection | numberDefect | oddGeneration |
      expressionEvaluation => 3
  | jacobiatorResolution | reflectionCancellation | braidingDefect | evenAssociatorRange |
      contextPropagation => 4
  | pathCorrection | signObstruction => 5

theorem edge_rank_lt {a b : Archetype} (h : Edge a b) : rank a < rank b := by
  cases h <;> decide

def Precedes : Archetype → Archetype → Prop := Relation.ReflTransGen Edge

theorem rank_mono {a b : Archetype} (h : Precedes a b) : rank a ≤ rank b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact le_trans ih (le_of_lt (edge_rank_lt h))

theorem eq_or_rank_lt {a b : Archetype} (h : Precedes a b) :
    a = b ∨ rank a < rank b := by
  cases h with
  | refl => exact Or.inl rfl
  | tail h e => exact Or.inr (lt_of_le_of_lt (rank_mono h) (edge_rank_lt e))

theorem precedes_antisymm {a b : Archetype} (hab : Precedes a b)
    (hba : Precedes b a) : a = b := by
  rcases eq_or_rank_lt hab with h | h
  · exact h
  · exact False.elim ((not_lt_of_ge (rank_mono hba)) h)

instance : PartialOrder Archetype where
  le := Precedes
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := precedes_antisymm

theorem edge_le {a b : Archetype} (h : Edge a b) : a ≤ b :=
  Relation.ReflTransGen.single h

theorem edge_strict {a b : Archetype} (h : Edge a b) : a < b := by
  exact lt_of_le_of_ne (edge_le h) (fun hab => by
    have := edge_rank_lt h
    rw [hab] at this
    exact (lt_irrefl _ this))

theorem no_strict_cycle {a b : Archetype} (h : Edge a b) : ¬ b ≤ a := by
  intro hba
  exact (not_lt_of_ge (rank_mono hba)) (edge_rank_lt h)

theorem operator_precedes_cancellation : operatorAlgebra ≤ reflectionCancellation :=
  le_trans (edge_le .operator_triples)
    (le_trans (edge_le .triples_cross) (edge_le .cross_cancellation))

theorem defects_precede_jacobiator : additiveBilinearity ≤ jacobiatorResolution :=
  le_trans (edge_le .additive_defects) (edge_le .defects_jacobiator)

theorem distinct_equal_rank_incomparable {a b : Archetype}
    (hne : a ≠ b) (hrank : rank a = rank b) : ¬ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro hab
    rcases eq_or_rank_lt hab with h | h
    · exact hne h
    · rw [hrank] at h
      exact lt_irrefl _ h
  · intro hba
    rcases eq_or_rank_lt hba with h | h
    · exact hne h.symm
    · rw [hrank] at h
      exact lt_irrefl _ h

theorem independent_first_branches :
    ¬ peirceCorners ≤ operatorTriples ∧ ¬ operatorTriples ≤ peirceCorners :=
  distinct_equal_rank_incomparable (by decide) rfl

theorem independent_terminal_branches :
    ¬ reflectionCancellation ≤ braidingDefect ∧
      ¬ braidingDefect ≤ reflectionCancellation :=
  distinct_equal_rank_incomparable (by decide) rfl

theorem operator_precedes_pathCorrection : operatorAlgebra ≤ pathCorrection :=
  le_trans (edge_le .operator_syntax)
    (le_trans (edge_le .syntax_evaluation)
      (le_trans (edge_le .evaluation_context) (edge_le .context_path)))

theorem independent_rotation_and_cross_branches :
    ¬ rotationOrder ≤ crossIdentities ∧ ¬ crossIdentities ≤ rotationOrder :=
  distinct_equal_rank_incomparable (by decide) rfl

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Rank 0–1 (`operatorAlgebra`, `additiveBilinearity`, `peirceCorners`, `operatorTriples`, `jordanProduct`, `universalDefects`, `expressionSyntax`):**
Universal Lie–Jordan bilinearity, Peirce corner nilpotency, and operator triple sandwiches
over `[Ring B]`. -/
theorem rank_0_to_1_operator_peirce_jordan_triples
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    comm X (Y * Z) = comm X Y * Z + Y * comm X Z ∧
    anticomm X (anticomm Y Z) - anticomm Y (anticomm X Z) = comm (comm X Y) Z ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    conePlus P A * coneMinus P C * conePlus P A = genV P A C * conePlus P A ∧
    coneMinus P C * conePlus P A * coneMinus P C = genV P A C * coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Rank 2–3 (`peirceGeometry`, `crossIdentities`, `zornProduct`, `jordanGeometry`, `rotationOrder`, `zornCorners`, `channelAssociators`, `reflection`, `numberDefect`, `oddGeneration`, `expressionEvaluation`):**
Zorn corner multiplication table, cross-sandwich identities, grading reflection `S_P`, and
odd-grade cubic generation over `[Ring B]`. -/
theorem rank_2_to_3_zorn_corners_reflection_and_odd_generation
    {P : B} (hP : P * P = P) (A C X : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C ∧
    sandwichCross P A C X - sandwichSame P A C X = -(genJ P A C * X * genJ P A C) ∧
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [sandwichCross, sandwichSame]; peirce_nf hP
  · simp only [sandwichCross, sandwichSame]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Rank 4–5 (`jacobiatorResolution`, `reflectionCancellation`, `braidingDefect`, `evenAssociatorRange`, `contextPropagation`, `pathCorrection`, `signObstruction`):**
Jacobiator vanishing, reflection cancellation `X + S_P * X * S_P = 2 • evenGrade P X`,
braiding commutator `[N_+, [N_-, X]] - [N_-, [N_+, X]] = [Σ, X]`, and sign obstruction
`[Φ, J] = -2 • Σ`. -/
theorem rank_4_to_5_jacobiator_reflection_and_braiding_obstruction
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
    X + invS P * X * invS P = (2 : ℤ) • evenGrade P X ∧
    comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · simp only [evenGrade]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Master Synthesis (`matrix_peirce_zorn_dependency_poset_master_synthesis`):**
Unites the 25-stage `Archetype` poset theorems with the non-commutative `[Ring B]`
Peirce–Zorn operator spine across all 6 ranks (`0 → 5`). -/
theorem matrix_peirce_zorn_dependency_poset_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (operatorAlgebra ≤ reflectionCancellation ∧
      additiveBilinearity ≤ jacobiatorResolution ∧
      operatorAlgebra ≤ pathCorrection) ∧
    (conePlus P A * coneMinus P C * conePlus P A = genV P A C * conePlus P A) ∧
    (sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C) ∧
    (comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X) := by
  have h1 := rank_0_to_1_operator_peirce_jordan_triples hP A C X Y Z
  have h2 := rank_2_to_3_zorn_corners_reflection_and_odd_generation hP A C X
  have h3 := rank_4_to_5_jacobiator_reflection_and_braiding_obstruction hP A C X Y Z
  exact ⟨⟨operator_precedes_cancellation, defects_precede_jacobiator,
      operator_precedes_pathCorrection⟩,
    h1.2.2.2.2.1, h2.2.2.1, h3.2.2.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Canonical.MatrixPeirceZorn.DependencyPoset
