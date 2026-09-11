import InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector

/-!
# Evaluator for the CAS flag-word transport

The GAP certificate uses generator numbers `1..8`: the six fixed PC
generators, `swap01Aut`, and `correctedT`.  This file owns the only Lean
evaluation interface for those words.  It deliberately proves no coverage
claim; membership, distinctness, and exhaustion remain separate obligations.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator

open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev FlagGenerator := Fin 8
abbrev FlagWord := List (FlagGenerator × Int)

def pcFlagGenerator (i : Fin 6) : FlagGenerator :=
  ⟨i.1, by omega⟩

noncomputable def flagGeneratorValue : FlagGenerator → SplitOctF2Aut
  | 0 => pcGenerator 0
  | 1 => pcGenerator 1
  | 2 => pcGenerator 2
  | 3 => pcGenerator 3
  | 4 => pcGenerator 4
  | 5 => pcGenerator 5
  | 6 => swap01Aut
  | 7 => correctedT

@[simp] theorem flagGeneratorValue_pc (i : Fin 6) :
    flagGeneratorValue (pcFlagGenerator i) = pcGenerator i := by
  fin_cases i <;> rfl

@[simp] theorem flagGeneratorValue_swap :
    flagGeneratorValue 6 = swap01Aut := rfl

@[simp] theorem flagGeneratorValue_corrected :
    flagGeneratorValue 7 = correctedT := rfl

noncomputable def evaluateToken (t : FlagGenerator × Int) : SplitOctF2Aut :=
  (flagGeneratorValue t.1) ^ t.2

@[simp] theorem evaluateToken_pc (i : Fin 6) (n : Int) :
    evaluateToken (pcFlagGenerator i, n) = (pcGenerator i) ^ n := by
  simp [evaluateToken, flagGeneratorValue_pc]

@[simp] theorem evaluateToken_swap (n : Int) :
    evaluateToken (6, n) = swap01Aut ^ n := by
  rfl

@[simp] theorem evaluateToken_corrected (n : Int) :
    evaluateToken (7, n) = correctedT ^ n := by
  rfl

noncomputable def evaluateWord (w : FlagWord) : SplitOctF2Aut :=
  (w.map evaluateToken).prod

def pcFlagWord (w : List (Fin 6 × Int)) : FlagWord :=
  w.map (fun t => (pcFlagGenerator t.1, t.2))

@[simp] theorem evaluateWord_nil : evaluateWord [] = 1 := rfl

theorem evaluateWord_cons (g : FlagGenerator × Int) (w : FlagWord) :
    evaluateWord (g :: w) = evaluateToken g * evaluateWord w := by
  rfl

theorem evaluateWord_pcFlagWord (w : List (Fin 6 × Int)) :
    evaluateWord (pcFlagWord w) =
      (w.map (fun t => (pcGenerator t.1) ^ t.2)).prod := by
  induction w with
  | nil => rfl
  | cons t w ih =>
      change evaluateToken (pcFlagGenerator t.1, t.2) *
          evaluateWord (pcFlagWord w) =
        (pcGenerator t.1) ^ t.2 *
          (w.map (fun t => (pcGenerator t.1) ^ t.2)).prod
      rw [evaluateToken_pc, ih]

theorem evaluateWord_pcFlagWord_eq_collect (w : List (Fin 6 × Int)) :
    evaluateWord (pcFlagWord w) = collect w := by
  rw [evaluateWord_pcFlagWord]
  exact (collect_eq_factor_product w).symm

def flagGeneratedSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range flagGeneratorValue)

theorem evaluateToken_mem_flagGeneratedSubgroup (t : FlagGenerator × Int) :
    evaluateToken t ∈ flagGeneratedSubgroup := by
  apply Subgroup.zpow_mem
  exact Subgroup.subset_closure ⟨t.1, rfl⟩

theorem evaluateWord_mem_flagGeneratedSubgroup (w : FlagWord) :
    evaluateWord w ∈ flagGeneratedSubgroup := by
  induction w with
  | nil => exact flagGeneratedSubgroup.one_mem
  | cons t w ih =>
      rw [evaluateWord_cons]
      exact flagGeneratedSubgroup.mul_mem
        (evaluateToken_mem_flagGeneratedSubgroup t) ih

theorem evaluateWord_append (u v : FlagWord) :
    evaluateWord (u ++ v) = evaluateWord u * evaluateWord v := by
  simp [evaluateWord, List.map_append, List.prod_append]

theorem evaluateToken_neg (g : FlagGenerator) (n : Int) :
    evaluateToken (g, -n) = (flagGeneratorValue g)⁻¹ ^ n := by
  simp [evaluateToken, zpow_neg]

end InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
