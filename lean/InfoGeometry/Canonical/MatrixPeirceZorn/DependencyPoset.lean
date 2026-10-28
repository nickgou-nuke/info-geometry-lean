/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.DeriveFintype

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
  deriving DecidableEq, Repr

open Archetype

instance : Fintype Archetype where
  elems := {operatorAlgebra, additiveBilinearity, peirceCorners, operatorTriples,
    jordanProduct, jordanGeometry, universalDefects, peirceGeometry, crossIdentities, zornProduct,
    zornCorners, channelAssociators, reflection, numberDefect, oddGeneration,
    evenAssociatorRange, jacobiatorResolution,
    reflectionCancellation, braidingDefect}
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

def rank : Archetype → ℕ
  | operatorAlgebra | additiveBilinearity => 0
  | peirceCorners | operatorTriples | jordanProduct | universalDefects => 1
  | peirceGeometry | crossIdentities | zornProduct | jordanGeometry => 2
  | zornCorners | channelAssociators | reflection | numberDefect | oddGeneration => 3
  | jacobiatorResolution | reflectionCancellation | braidingDefect | evenAssociatorRange => 4

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

end InfoGeometry.Canonical.MatrixPeirceZorn.DependencyPoset
