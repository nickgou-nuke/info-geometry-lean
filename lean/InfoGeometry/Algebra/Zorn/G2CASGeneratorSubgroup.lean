import InfoGeometry.Algebra.Zorn.G2CASGeneratorAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator

/-!
# Native subgroup containment for the CAS six-generator chart

The six CAS generators are already native words in the eight-generator Lean
carrier.  This owner records the resulting subgroup containment explicitly;
it does not identify the CAS Sylow subgroup with the native PC subgroup.
-/

namespace InfoGeometry.Algebra.Zorn.G2CASGeneratorSubgroup

open InfoGeometry.Algebra.Zorn.G2CASGeneratorAlignment
open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def casGenerator : Fin 6 → SplitOctF2Aut
  | 0 => cas0
  | 1 => cas1
  | 2 => cas2
  | 3 => cas3
  | 4 => cas4
  | 5 => cas5

def casGeneratedSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range casGenerator)

theorem cas0_mem_flagGeneratedSubgroup : cas0 ∈ flagGeneratedSubgroup := by
  simpa [cas0, evaluateWord, evaluateToken, flagGeneratorValue] using
    (evaluateWord_mem_flagGeneratedSubgroup [(7, 1)])

theorem cas1_mem_flagGeneratedSubgroup : cas1 ∈ flagGeneratedSubgroup := by
  simpa [cas1, evaluateWord, evaluateToken, flagGeneratorValue] using
    (evaluateWord_mem_flagGeneratedSubgroup
      [(3, 1), (7, 1), (6, 1), (7, 1), (1, -1), (6, 1), (1, 1), (7, 1)])

theorem cas2_mem_flagGeneratedSubgroup : cas2 ∈ flagGeneratedSubgroup := by
  simpa [cas2, evaluateWord, evaluateToken, flagGeneratorValue] using
    (evaluateWord_mem_flagGeneratedSubgroup
      [(0, 1), (7, 1), (6, 1), (2, 1), (7, 1), (6, 1),
       (7, 1), (6, 1), (1, -1)])

theorem cas3_mem_flagGeneratedSubgroup : cas3 ∈ flagGeneratedSubgroup := by
  simpa [cas3, evaluateWord, evaluateToken, flagGeneratorValue] using
    (evaluateWord_mem_flagGeneratedSubgroup
      [(3, 1), (7, 1), (6, 1), (7, 1), (3, 1)])

theorem cas4_mem_flagGeneratedSubgroup : cas4 ∈ flagGeneratedSubgroup := by
  simpa [cas4, evaluateWord, evaluateToken, flagGeneratorValue] using
    (evaluateWord_mem_flagGeneratedSubgroup
      [(7, 1), (2, 1), (6, 1), (7, 1), (2, 1), (6, 1), (2, 1), (7, 1)])

theorem cas5_mem_flagGeneratedSubgroup : cas5 ∈ flagGeneratedSubgroup := by
  simpa [cas5, evaluateWord, evaluateToken, flagGeneratorValue] using
    (evaluateWord_mem_flagGeneratedSubgroup
      [(7, 1), (6, 1), (7, 1), (6, 1), (7, 1)])

theorem casGeneratedSubgroup_le_flagGeneratedSubgroup :
    casGeneratedSubgroup ≤ flagGeneratedSubgroup := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, rfl⟩
  fin_cases i
  · exact cas0_mem_flagGeneratedSubgroup
  · exact cas1_mem_flagGeneratedSubgroup
  · exact cas2_mem_flagGeneratedSubgroup
  · exact cas3_mem_flagGeneratedSubgroup
  · exact cas4_mem_flagGeneratedSubgroup
  · exact cas5_mem_flagGeneratedSubgroup

private theorem list_prod_mem_of_mem (K : Subgroup SplitOctF2Aut)
    (l : List SplitOctF2Aut) (h : ∀ x ∈ l, x ∈ K) : l.prod ∈ K := by
  induction l with
  | nil => exact K.one_mem
  | cons x xs ih =>
      rw [List.prod_cons]
      exact K.mul_mem (h x (List.mem_cons_self))
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem cas_mem_casGeneratedSubgroup (i : Fin 6) :
    casGenerator i ∈ casGeneratedSubgroup := by
  fin_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩
  · exact Subgroup.subset_closure ⟨3, rfl⟩
  · exact Subgroup.subset_closure ⟨4, rfl⟩
  · exact Subgroup.subset_closure ⟨5, rfl⟩

theorem pcGenerator_zero_mem_casGeneratedSubgroup :
    pcGenerator 0 ∈ casGeneratedSubgroup := by
  rw [pcGenerator_zero_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup [cas5, cas4, cas2, cas0, cas5] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 4
      · exact cas_mem_casGeneratedSubgroup 2
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 5))

theorem pcGenerator_one_mem_casGeneratedSubgroup :
    pcGenerator 1 ∈ casGeneratedSubgroup := by
  rw [pcGenerator_one_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup
      [cas0, cas1, cas5, cas3, cas4, cas2, cas5, cas4] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 1
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 3
      · exact cas_mem_casGeneratedSubgroup 4
      · exact cas_mem_casGeneratedSubgroup 2
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 4))

theorem pcGenerator_two_mem_casGeneratedSubgroup :
    pcGenerator 2 ∈ casGeneratedSubgroup := by
  rw [pcGenerator_two_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup
      [cas0, cas5, cas4, cas0, cas5, cas4, cas2, cas5] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 4
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 4
      · exact cas_mem_casGeneratedSubgroup 2
      · exact cas_mem_casGeneratedSubgroup 5))

theorem pcGenerator_three_mem_casGeneratedSubgroup :
    pcGenerator 3 ∈ casGeneratedSubgroup := by
  rw [pcGenerator_three_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup
      [cas5, cas0, cas1, cas0, cas1, cas5] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 1
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 1
      · exact cas_mem_casGeneratedSubgroup 5))

theorem pcGenerator_four_mem_casGeneratedSubgroup :
    pcGenerator 4 ∈ casGeneratedSubgroup := by
  rw [pcGenerator_four_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup [cas5, cas0, cas4, cas2, cas5] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 4
      · exact cas_mem_casGeneratedSubgroup 2
      · exact cas_mem_casGeneratedSubgroup 5))

theorem pcGenerator_five_mem_casGeneratedSubgroup :
    pcGenerator 5 ∈ casGeneratedSubgroup := by
  rw [pcGenerator_five_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup [cas5, cas3, cas5] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 3
      · exact cas_mem_casGeneratedSubgroup 5))

theorem swap01Aut_mem_casGeneratedSubgroup :
    swap01Aut ∈ casGeneratedSubgroup := by
  rw [swap01Aut_eq_cas_word]
  simpa [List.prod_cons, mul_assoc] using
    (list_prod_mem_of_mem casGeneratedSubgroup
      [cas1, cas5, cas1, cas0, cas3, cas5, cas1] (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cas_mem_casGeneratedSubgroup 1
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 1
      · exact cas_mem_casGeneratedSubgroup 0
      · exact cas_mem_casGeneratedSubgroup 3
      · exact cas_mem_casGeneratedSubgroup 5
      · exact cas_mem_casGeneratedSubgroup 1))

theorem correctedT_mem_casGeneratedSubgroup :
    correctedT ∈ casGeneratedSubgroup := by
  simpa [cas0, casGenerator] using cas_mem_casGeneratedSubgroup 0

theorem flagGeneratedSubgroup_le_casGeneratedSubgroup :
    flagGeneratedSubgroup ≤ casGeneratedSubgroup := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact pcGenerator_zero_mem_casGeneratedSubgroup
  · exact pcGenerator_one_mem_casGeneratedSubgroup
  · exact pcGenerator_two_mem_casGeneratedSubgroup
  · exact pcGenerator_three_mem_casGeneratedSubgroup
  · exact pcGenerator_four_mem_casGeneratedSubgroup
  · exact pcGenerator_five_mem_casGeneratedSubgroup
  · exact swap01Aut_mem_casGeneratedSubgroup
  · exact correctedT_mem_casGeneratedSubgroup

theorem casGeneratedSubgroup_eq_flagGeneratedSubgroup :
    casGeneratedSubgroup = flagGeneratedSubgroup :=
  le_antisymm casGeneratedSubgroup_le_flagGeneratedSubgroup
    flagGeneratedSubgroup_le_casGeneratedSubgroup

end InfoGeometry.Algebra.Zorn.G2CASGeneratorSubgroup
