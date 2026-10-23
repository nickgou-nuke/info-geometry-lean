/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2ReducedWords
import InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

/-! Reduced-word length for the corrected native simple-generator pair. -/
namespace InfoGeometry.Algebra.Zorn.G2CorrectedWordLength

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2ConcreteWeylG2 G2TwoBruhatClassification G2ReducedWords
open G2ConcreteBN2CorrectSecondConjugation

def reindex (p : WeylG2) : WeylG2 := (-p.1, p.2)

def correctedLength (p : WeylG2) : ℕ := dihedralLength (reindex p)

noncomputable def generator (b : Bool) : SplitOctF2Aut :=
  if b then s else correctedT

def step (b : Bool) (p : WeylG2) : WeylG2 :=
  let a : ZMod 6 := if b then 0 else 5
  (if p.2 then p.1 - a else a + p.1, !p.2)

def wordIndex : List Bool → WeylG2
  | [] => (0, false)
  | b :: L => step b (wordIndex L)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem step_evaluation : ∀ (b : Bool) (p : WeylG2),
    weylNF (step b p).1 (step b p).2 = generator b * weylNF p.1 p.2 := by
  intro b p
  apply automorphism_ext_of_basis
  intro i
  revert i p b
  decide

theorem step_length_bound : ∀ (b : Bool) (p : WeylG2),
    correctedLength (step b p) ≤ correctedLength p + 1 := by
  decide

theorem wordIndex_evaluation (L : List Bool) :
    weylNF (wordIndex L).1 (wordIndex L).2 = (L.map generator).prod := by
  induction L with
  | nil => exact weylNF_zero_false
  | cons b L ih =>
      change weylNF (step b (wordIndex L)).1 (step b (wordIndex L)).2 = _
      rw [step_evaluation, ih]
      rfl

theorem wordIndex_length_le (L : List Bool) :
    correctedLength (wordIndex L) ≤ L.length := by
  induction L with
  | nil => decide
  | cons b L ih =>
      exact (step_length_bound b (wordIndex L)).trans (Nat.add_le_add_right ih 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem chosen_word_evaluation : ∀ p : WeylG2,
    ((toReducedWord (reindex p)).map generator).prod = weylNF p.1 p.2 := by
  intro p
  apply automorphism_ext_of_basis
  intro i
  revert i p
  decide

theorem minimal_length (p : WeylG2) (L : List Bool)
    (h : (L.map generator).prod = weylNF p.1 p.2) :
    correctedLength p ≤ L.length := by
  have hp : wordIndex L = p :=
    weylNF_injective ((wordIndex_evaluation L).trans h)
  rw [← hp]
  exact wordIndex_length_le L

/-- The bound is attained by an explicitly evaluated native generator word. -/
theorem exists_minimal_word (p : WeylG2) :
    ∃ L : List Bool, (L.map generator).prod = weylNF p.1 p.2 ∧
      L.length = correctedLength p ∧
      ∀ K : List Bool, (K.map generator).prod = weylNF p.1 p.2 → L.length ≤ K.length := by
  exact ⟨toReducedWord (reindex p), chosen_word_evaluation p, rfl,
    fun K hK => minimal_length p K hK⟩

end InfoGeometry.Algebra.Zorn.G2CorrectedWordLength
