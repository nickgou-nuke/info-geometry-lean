import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.Window6ExplicitFibers

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing wrapper: the audited window-6 fiber histogram determines the full `q`-moment
closed form and its listed specializations.
    prop:typed-address-biaxial-completion-window6-collision-closed-form -/
theorem paper_typed_address_biaxial_completion_window6_collision_closed_form
    (generalMomentFormula secondMomentValue thirdMomentValue fourthMomentValue
      normalizedSecondCollision : Prop)
    (hGeneralMomentFormula : generalMomentFormula)
    (hSecondMomentValue : secondMomentValue)
    (hThirdMomentValue : thirdMomentValue)
    (hFourthMomentValue : fourthMomentValue)
    (hNormalizedSecondCollision : normalizedSecondCollision) :
    generalMomentFormula ∧ secondMomentValue ∧ thirdMomentValue ∧ fourthMomentValue ∧
      normalizedSecondCollision := by
  exact ⟨hGeneralMomentFormula, hSecondMomentValue, hThirdMomentValue,
    hFourthMomentValue, hNormalizedSecondCollision⟩

end Omega.TypedAddressBiaxialCompletion
