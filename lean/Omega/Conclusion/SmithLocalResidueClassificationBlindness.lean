import Mathlib.Tactic
import Omega.Conclusion.SmithLocalZetaPoleResidueHeadTriple

namespace Omega.Conclusion

open Omega.Zeta

/-- The local Smith spectrum `(2,1,0)` used in the residue-blindness comparison. -/
def conclusion_smith_local_residue_classification_blindness_spectrum210 : Fin 3 → ℕ :=
  ![2, 1, 0]

/-- The local Smith spectrum `(1,1,1)` used in the residue-blindness comparison. -/
def conclusion_smith_local_residue_classification_blindness_spectrum111 : Fin 3 → ℕ :=
  ![1, 1, 1]

/-- Paper label: `prop:conclusion-smith-local-residue-classification-blindness`.
The spectra `(2,1,0)` and `(1,1,1)` have the same total `p`-mass, hence the same residue, but
their maximal local height and first platform length differ. -/
theorem paper_conclusion_smith_local_residue_classification_blindness (p : ℕ) :
    conclusion_smith_local_zeta_pole_residue_head_triple_residue p
        conclusion_smith_local_residue_classification_blindness_spectrum210 =
      conclusion_smith_local_zeta_pole_residue_head_triple_residue p
        conclusion_smith_local_residue_classification_blindness_spectrum111 ∧
    conclusion_smith_local_zeta_pole_residue_head_triple_head
        conclusion_smith_local_residue_classification_blindness_spectrum210 = 2 ∧
    conclusion_smith_local_zeta_pole_residue_head_triple_head
        conclusion_smith_local_residue_classification_blindness_spectrum111 = 1 ∧
    smithPrefixValue conclusion_smith_local_residue_classification_blindness_spectrum210 1 = 2 ∧
    smithPrefixValue conclusion_smith_local_residue_classification_blindness_spectrum111 1 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_smith_local_zeta_pole_residue_head_triple_residue,
      Fin.sum_univ_three,
      conclusion_smith_local_residue_classification_blindness_spectrum210,
      conclusion_smith_local_residue_classification_blindness_spectrum111]
  · unfold conclusion_smith_local_zeta_pole_residue_head_triple_head smithPrefixTop
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro i hi
      fin_cases i <;> decide
    · have hzero := Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
        (f := conclusion_smith_local_residue_classification_blindness_spectrum210)
        (by decide : (0 : Fin 3) ∈ Finset.univ)
      exact hzero
  · unfold conclusion_smith_local_zeta_pole_residue_head_triple_head smithPrefixTop
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro i hi
      fin_cases i <;> decide
    · have hzero := Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
        (f := conclusion_smith_local_residue_classification_blindness_spectrum111)
        (by decide : (0 : Fin 3) ∈ Finset.univ)
      exact hzero
  · simp [smithPrefixValue, Fin.sum_univ_three,
      conclusion_smith_local_residue_classification_blindness_spectrum210]
  · simp [smithPrefixValue, Fin.sum_univ_three,
      conclusion_smith_local_residue_classification_blindness_spectrum111]

end Omega.Conclusion
