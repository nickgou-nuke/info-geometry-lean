import InfoGeometry.Clifford.Pin55ReflectionGlide
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Physics.ZornTkkOrchestration

open InfoGeometry.Clifford.Pin55ReflectionGlide

structure DefectSheetState where
  sheet : Bool
  carrier : Split55

def defectSheetTransition (s : DefectSheetState) : DefectSheetState where
  sheet := !s.sheet
  carrier := pinReflection s.carrier

@[simp] theorem defectSheetTransition_sheet (s : DefectSheetState) :
    (defectSheetTransition s).sheet = !s.sheet := by
  rfl

@[simp] theorem defectSheetTransition_carrier (s : DefectSheetState) :
    (defectSheetTransition s).carrier = pinReflection s.carrier := by
  rfl

theorem defectSheetTransition_involutive : Function.Involutive defectSheetTransition := by
  intro s
  cases s
  simp [defectSheetTransition, pinReflection_involutive]

theorem defectSheetTransition_preserves_splitPair (s t : DefectSheetState) :
    splitPair (defectSheetTransition s).carrier (defectSheetTransition t).carrier =
      splitPair s.carrier t.carrier := by
  simp [defectSheetTransition, pinReflection_preserves_splitPair]

def defectSheetGlide (s : DefectSheetState) : DefectSheetState where
  sheet := s.sheet
  carrier := glide s.carrier

@[simp] theorem defectSheetGlide_sheet (s : DefectSheetState) :
    (defectSheetGlide s).sheet = s.sheet := by
  rfl

@[simp] theorem defectSheetGlide_carrier (s : DefectSheetState) :
    (defectSheetGlide s).carrier = glide s.carrier := by
  rfl

theorem defectSheetGlide_square_eq_translation (s : DefectSheetState) :
    defectSheetGlide (defectSheetGlide s) =
      { s with carrier := translateP 1 s.carrier } := by
  cases s
  simp [defectSheetGlide, glide_square_eq_translation]

theorem defectRunway_packet (s : DefectSheetState) :
    defectSheetTransition (defectSheetTransition s) = s ∧
      splitPair (defectSheetTransition s).carrier (defectSheetTransition s).carrier =
        splitPair s.carrier s.carrier ∧
      defectSheetGlide (defectSheetGlide s) = { s with carrier := translateP 1 s.carrier } := by
  refine ⟨?_, ?_, ?_⟩
  · exact defectSheetTransition_involutive s
  · simpa using defectSheetTransition_preserves_splitPair s s
  · exact defectSheetGlide_square_eq_translation s

end InfoGeometry.Physics.ZornTkkOrchestration
