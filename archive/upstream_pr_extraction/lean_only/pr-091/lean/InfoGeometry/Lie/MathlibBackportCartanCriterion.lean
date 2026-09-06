module

public import InfoGeometry.Lie.MathlibBackportCartanCriterionFull

/-!
# Compatibility layer for Cartan's semisimplicity criterion

The preceding local owner supplies the trace-form and solvability lemmas that
are absent from the pinned Mathlib snapshot.  This file exports the final
InfoGeometry-owned compatibility instance and its explicit hypothesis form.
-/

noncomputable section

public section

namespace InfoGeometry.Lie.MathlibBackportCartanCriterion

variable {R L : Type*}
  [CommRing R]
  [LieRing L] [LieAlgebra R L]

theorem isKilling_of_hasTrivialRadical_of_killingCompl_top_le_radical
    [LieAlgebra.HasTrivialRadical R L]
    (h : LieIdeal.killingCompl R L ⊤ ≤ LieAlgebra.radical R L) :
    LieAlgebra.IsKilling R L := by
  refine ⟨?_⟩
  apply le_antisymm
  · calc
      LieIdeal.killingCompl R L ⊤ ≤ LieAlgebra.radical R L := h
      _ = ⊥ := LieAlgebra.HasTrivialRadical.radical_eq_bot
  · exact bot_le

/- The compatibility instance is exported under an InfoGeometry-owned name as
   well, so consumers need not depend on the later Mathlib declaration name. -/
end InfoGeometry.Lie.MathlibBackportCartanCriterion
