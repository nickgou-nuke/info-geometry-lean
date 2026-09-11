import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator

/-! The CAS word table evaluated in the exact Lean carrier.  No theorem about
    injectivity or coverage is bundled with this definition. -/

namespace InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def flagRepresentative : Fin 189 → SplitOctF2Aut :=
  fun i => evaluateWord (flagRepWords i)

theorem flagRepresentative_mem (i : Fin 189) :
    flagRepresentative i ∈ flagGeneratedSubgroup := by
  exact evaluateWord_mem_flagGeneratedSubgroup (flagRepWords i)

/-! A native decomposition lemma for later predecessor certificates.  The
    index relation is intentionally left explicit: this theorem proves the
    algebraic word step, while a separate certificate must identify the
    suffix with a valid predecessor in the same cell. -/
theorem flagRepresentative_eq_token_mul_of_word_eq_cons
    (i : Fin 189) (g : FlagGenerator × Int) (w : FlagWord)
    (h : flagRepWords i = g :: w) :
    flagRepresentative i = evaluateToken g * evaluateWord w := by
  unfold flagRepresentative
  rw [h, evaluateWord_cons]

theorem flagRepresentative_eq_generator_mul_of_predecessor_word
    (i j : Fin 189) (g : FlagGenerator)
    (h : flagRepWords i = (g, 1) :: flagRepWords j) :
    flagRepresentative i = flagGeneratorValue g * flagRepresentative j := by
  unfold flagRepresentative
  rw [h, evaluateWord_cons]
  simp [evaluateToken]

/-! The first genuine same-cell word seam is suffix-oriented: the word at
    index 2 extends the word at index 1 by the two-token suffix `(4,1),(1,1)`.
    This is intentionally kept at the word/evaluator boundary; factorized
    compatibility is a separate obligation. -/
theorem flagRepWords_2_eq_append_1 :
    flagRepWords (2 : Fin 189) =
      flagRepWords (1 : Fin 189) ++ [((4 : Fin 8), 1), ((1 : Fin 8), 1)] := by
  decide

theorem flagRepresentative_2_eq_right_step_1 :
    flagRepresentative (2 : Fin 189) =
      flagRepresentative (1 : Fin 189) *
        evaluateWord [((4 : Fin 8), 1), ((1 : Fin 8), 1)] := by
  unfold flagRepresentative
  rw [flagRepWords_2_eq_append_1, evaluateWord_append]


set_option maxRecDepth 100000 in
theorem flagCells_partition :
    Finset.univ.biUnion flagCells = Finset.univ := by
  decide

def flagCellCard : Fin 12 → Nat
  | 0 => 1
  | 1 => 4
  | 2 => 16
  | 3 => 64
  | 4 => 16
  | 5 => 4
  | 6 => 2
  | 7 => 2
  | 8 => 8
  | 9 => 32
  | 10 => 32
  | 11 => 8

set_option maxRecDepth 100000 in
theorem flagCells_card (k : Fin 12) :
    (flagCells k).card = flagCellCard k := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
theorem flagCells_total_card :
    (∑ k : Fin 12, (flagCells k).card) = 189 := by
  native_decide

set_option maxRecDepth 100000 in
theorem flagCells_pairwise_disjoint :
    ∀ ⦃i j : Fin 12⦄, i ≠ j → Disjoint (flagCells i) (flagCells j) := by
  native_decide

end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
