import InfoGeometry.Exceptional.CuntzArchimedeanColimit

namespace InfoGeometry.Exceptional.CuntzArchimedeanColimitTests

open InfoGeometry.Clifford CuntzArchimedeanColimit

example : InfoGeometry.Clifford.norm (⟨0, 0, 1, 1⟩ : SplitQuaternion) = -2 := by
  dsimp [InfoGeometry.Clifford.norm]
  norm_num

example : InfoGeometry.Clifford.norm (⟨0, 0, 1, 1⟩ : SplitQuaternion) ≠ 0 := by
  dsimp [InfoGeometry.Clifford.norm]
  norm_num

example : (⟨0, 1, 1, 0⟩ : SplitQuaternion) ≠ 0 := by
  intro equality
  have coordinate := congrArg SplitQuaternion.x equality
  change (1 : ℝ) = 0 at coordinate
  norm_num at coordinate

#print axioms cuntz_branches_orthogonal
#print axioms no_normalized_real_trace
#print axioms equal_negative_coordinates_null_iff
#print axioms opposite_signature_coordinates_square_zero

end InfoGeometry.Exceptional.CuntzArchimedeanColimitTests
