import InfoGeometry.Clifford.Cl55RealSplitPinReflectionEvidence

namespace InfoGeometry.Clifford.Clifford55

/-!
# The finite orthogonal reflection subgroup lies in the corrected split image

The result is deliberately one-sided: the explicit coordinate reflection
subgroup is proved to be contained in the image of the corrected split Pin
action.  No equality with the full orthogonal group is asserted here.
-/

noncomputable def realSplitPinOrthogonalImage : Subgroup orthogonalGroup55 :=
  (realSplitPinOrthogonalAction).range

theorem coordinateReflectionGenerator_mem_realSplitPinOrthogonalImage
    (i : Fin 5) :
    coordinateReflectionGenerator i ∈ realSplitPinOrthogonalImage := by
  rcases realSplitPinOrthogonalAction_fNeg i with ⟨g, hg⟩
  exact ⟨g, hg⟩

theorem coordinateReflectionSubgroup_le_realSplitPinOrthogonalImage :
    coordinateReflectionSubgroup ≤ realSplitPinOrthogonalImage := by
  refine (Subgroup.closure_le realSplitPinOrthogonalImage).2 ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact coordinateReflectionGenerator_mem_realSplitPinOrthogonalImage i

theorem globalSheetReflectionGenerator_mem_realSplitPinOrthogonalImage :
    globalSheetReflectionGenerator ∈ realSplitPinOrthogonalImage := by
  rcases realSplitPinOrthogonalAction_globalSheet with ⟨g, hg⟩
  exact ⟨g, hg⟩

end InfoGeometry.Clifford.Clifford55
