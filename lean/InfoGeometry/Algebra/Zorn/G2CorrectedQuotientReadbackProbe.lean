import InfoGeometry.Algebra.Zorn.G2CorrectedQuotientCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2CorrectedQuotientReadbackProbe

open InfoGeometry.Algebra.Zorn.G2CorrectedQuotientCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

theorem group_eq_of_autMatrix_eq
    {f g : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut}
    (h : autMatrix f = autMatrix g) : f = g :=
  autMatrix_injective h

/-! A single concrete regression probe.  This is deliberately not promoted to
    a quotient theorem until the GAP/Lean word convention is reconciled. -/
theorem pair_12_57_matrix_distinct :
    autMatrix (correctedQuotientRepresentative 12) ≠
      autMatrix (correctedQuotientRepresentative 57) := by
  decide

theorem pair_12_57_group_distinct :
    correctedQuotientRepresentative 12 ≠
      correctedQuotientRepresentative 57 := by
  intro h
  apply pair_12_57_matrix_distinct
  exact congrArg autMatrix h

theorem pair_12_57_entry_separator :
    ∃ i j : Fin 8,
      autMatrix (correctedQuotientRepresentative 12) i j ≠
        autMatrix (correctedQuotientRepresentative 57) i j := by
  by_contra h
  apply pair_12_57_matrix_distinct
  ext i j
  by_contra hij
  exact h ⟨i, j, hij⟩

noncomputable def pair_12_57_separator : Fin 8 × Fin 8 :=
  (Classical.choose pair_12_57_entry_separator,
    Classical.choose (Classical.choose_spec pair_12_57_entry_separator))

theorem pair_12_57_separator_spec :
    autMatrix (correctedQuotientRepresentative 12)
        pair_12_57_separator.1 pair_12_57_separator.2 ≠
      autMatrix (correctedQuotientRepresentative 57)
        pair_12_57_separator.1 pair_12_57_separator.2 :=
  Classical.choose_spec (Classical.choose_spec pair_12_57_entry_separator)

end InfoGeometry.Algebra.Zorn.G2CorrectedQuotientReadbackProbe
