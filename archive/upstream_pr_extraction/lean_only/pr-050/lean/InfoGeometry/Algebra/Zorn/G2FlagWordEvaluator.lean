import InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
import InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

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
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev FlagGenerator := Fin 8
abbrev FlagWord := List (FlagGenerator × Int)

noncomputable def flagGeneratorValue : FlagGenerator → SplitOctF2Aut
  | 0 => pcGenerator 0
  | 1 => pcGenerator 1
  | 2 => pcGenerator 2
  | 3 => pcGenerator 3
  | 4 => pcGenerator 4
  | 5 => pcGenerator 5
  | 6 => swap01Aut
  | 7 => correctedT

noncomputable def evaluateToken (t : FlagGenerator × Int) : SplitOctF2Aut :=
  (flagGeneratorValue t.1) ^ t.2

noncomputable def evaluateWord (w : FlagWord) : SplitOctF2Aut :=
  (w.map evaluateToken).prod

@[simp] theorem evaluateWord_nil : evaluateWord [] = 1 := rfl

theorem evaluateWord_cons (g : FlagGenerator × Int) (w : FlagWord) :
    evaluateWord (g :: w) = evaluateToken g * evaluateWord w := by
  rfl

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
