import InfoGeometry.Canonical.SplitG2MetricDerivedHodgeStar
import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Determinant

namespace InfoGeometry.Canonical

/-!
# Native split-G2 top-degree volume form

The imaginary carrier already owns its finite-dimensionality theorem.  This
file only reindexes the native `Basis.ofVectorSpace` and derives the oriented
top-degree form from `Basis.det`; it does not introduce a second metric or
Hodge operator.
-/

abbrev SplitForm7 := AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 7)

noncomputable def imaginarySplitOctonionBasis :
    Module.Basis (Fin 7) ℚ imaginarySplitOctonion := by
  let b0 : Module.Basis
      (Module.Basis.ofVectorSpaceIndex ℚ imaginarySplitOctonion)
      ℚ imaginarySplitOctonion :=
    Module.Basis.ofVectorSpace ℚ imaginarySplitOctonion
  have hcard :
      Fintype.card (Module.Basis.ofVectorSpaceIndex ℚ imaginarySplitOctonion) = 7 := by
    have hb := Module.finrank_eq_card_basis b0
    rw [imaginarySplitOctonion_finrank_eq_seven] at hb
    exact hb.symm
  exact b0.reindex (Fintype.equivFinOfCardEq hcard)

noncomputable def splitG2VolumeForm : SplitForm7 :=
  (imaginarySplitOctonionBasis).det

@[simp] theorem splitG2VolumeForm_basis :
    splitG2VolumeForm
        (fun i => imaginarySplitOctonionBasis i) = 1 := by
  simpa [splitG2VolumeForm] using
    (Module.Basis.det_self imaginarySplitOctonionBasis)

theorem splitG2VolumeForm_ne_zero : splitG2VolumeForm ≠ 0 := by
  intro h
  have h' := congrArg
    (fun ω : SplitForm7 => ω (fun i => imaginarySplitOctonionBasis i)) h
  simpa using h'

end InfoGeometry.Canonical
