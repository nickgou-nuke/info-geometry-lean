import Mathlib.Tactic

namespace Omega.GU

/-- Paper-facing boundary-orientation multiplicativity wrapper: determinant realization and
parity reduction produce the two-cover jumpclass formula, from which the left-even specialization
and the double-even vanishing follow.
    prop:bdry-orientation-jumpclass-fiberproduct-multiplicativity -/
theorem paper_bdry_orientation_jumpclass_fiberproduct_multiplicativity
    (determinantRealization jumpclassAsStiefelWhitney tensorProductDeterminantFormula
      modTwoParityReduction jumpclassFormula leftEvenSpecialization doubleEvenVanishing : Prop)
    (hDeterminantRealization : determinantRealization)
    (hJumpclassAsStiefelWhitney : jumpclassAsStiefelWhitney)
    (hTensorProductDeterminantFormula : tensorProductDeterminantFormula)
    (hModTwoParityReduction : modTwoParityReduction)
    (deriveJumpclassFormula : determinantRealization → jumpclassAsStiefelWhitney →
      tensorProductDeterminantFormula → modTwoParityReduction → jumpclassFormula)
    (specializeLeftEven : jumpclassFormula → leftEvenSpecialization)
    (deriveDoubleEvenVanishing : jumpclassFormula → leftEvenSpecialization →
      doubleEvenVanishing) :
    jumpclassFormula ∧ leftEvenSpecialization ∧ doubleEvenVanishing := by
  have hFormula : jumpclassFormula :=
    deriveJumpclassFormula hDeterminantRealization hJumpclassAsStiefelWhitney
      hTensorProductDeterminantFormula hModTwoParityReduction
  have hLeftEven : leftEvenSpecialization := specializeLeftEven hFormula
  exact ⟨hFormula, hLeftEven, deriveDoubleEvenVanishing hFormula hLeftEven⟩

theorem paper_bdry_orientation_torsor_determinant_realization_jumpclass
    (determinantRealization jumpclassAsStiefelWhitney : Prop)
    (hDeterminantRealization : determinantRealization)
    (hJumpclassAsStiefelWhitney : jumpclassAsStiefelWhitney) :
    determinantRealization ∧ jumpclassAsStiefelWhitney := by
  exact ⟨hDeterminantRealization, hJumpclassAsStiefelWhitney⟩

end Omega.GU
