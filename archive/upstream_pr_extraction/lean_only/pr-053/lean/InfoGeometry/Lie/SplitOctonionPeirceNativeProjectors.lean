import InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

open InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter
open InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge

abbrev Carrier := InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.Carrier
abbrev CarrierEnd := Module.End ℝ Carrier

def projectorPP : CarrierEnd :=
  (1 / 4 : ℝ) • (1 + peirceSheetParity + exteriorDegreeParity + peirceCharacterProduct)
def projectorPM : CarrierEnd :=
  (1 / 4 : ℝ) • (1 + peirceSheetParity - exteriorDegreeParity - peirceCharacterProduct)
def projectorMP : CarrierEnd :=
  (1 / 4 : ℝ) • (1 - peirceSheetParity + exteriorDegreeParity - peirceCharacterProduct)
def projectorMM : CarrierEnd :=
  (1 / 4 : ℝ) • (1 - peirceSheetParity - exteriorDegreeParity + peirceCharacterProduct)

@[simp] theorem projectorPP_apply (x : Carrier) :
    projectorPP x = ![x 0, 0, 0, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [projectorPP, peirceCharacterProduct,
    InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.peirceSheetParity_apply,
    exteriorDegreeParity,
    Module.End.mul_apply] <;> ring

@[simp] theorem projectorPM_apply (x : Carrier) :
    projectorPM x = ![0, x 1, x 2, x 3, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [projectorPM, peirceCharacterProduct,
    InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.peirceSheetParity_apply,
    exteriorDegreeParity,
    Module.End.mul_apply] <;> ring

@[simp] theorem projectorMP_apply (x : Carrier) :
    projectorMP x = ![0, 0, 0, 0, x 4, x 5, x 6, 0] := by
  ext i
  fin_cases i <;> simp [projectorMP, peirceCharacterProduct,
    InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.peirceSheetParity_apply,
    exteriorDegreeParity,
    Module.End.mul_apply] <;> ring

@[simp] theorem projectorMM_apply (x : Carrier) :
    projectorMM x = ![0, 0, 0, 0, 0, 0, 0, x 7] := by
  ext i
  fin_cases i <;> simp [projectorMM, peirceCharacterProduct,
    InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.peirceSheetParity_apply,
    exteriorDegreeParity,
    Module.End.mul_apply] <;> ring

theorem projectorPP_idempotent : projectorPP * projectorPP = projectorPP := by
  ext x i
  fin_cases i <;> simp [Module.End.mul_apply]
theorem projectorPM_idempotent : projectorPM * projectorPM = projectorPM := by
  ext x i
  fin_cases i <;> simp [Module.End.mul_apply]
theorem projectorMP_idempotent : projectorMP * projectorMP = projectorMP := by
  ext x i
  fin_cases i <;> simp [Module.End.mul_apply]
theorem projectorMM_idempotent : projectorMM * projectorMM = projectorMM := by
  ext x i
  fin_cases i <;> simp [Module.End.mul_apply]

theorem projectors_pairwise_orthogonal :
    projectorPP * projectorPM = 0 ∧ projectorPP * projectorMP = 0 ∧
    projectorPP * projectorMM = 0 ∧ projectorPM * projectorMP = 0 ∧
    projectorPM * projectorMM = 0 ∧ projectorMP * projectorMM = 0 := by
  repeat' constructor
  all_goals ext x i <;> fin_cases i <;> simp [Module.End.mul_apply]

theorem projectors_complete :
    projectorPP + projectorPM + projectorMP + projectorMM = (1 : CarrierEnd) := by
  ext x i
  fin_cases i <;> simp

theorem sheetParity_projectorPP : peirceSheetParity * projectorPP = projectorPP := by
  ext x i; fin_cases i <;> simp [peirceSheetParity_apply, Module.End.mul_apply]
theorem degreeParity_projectorPP : exteriorDegreeParity * projectorPP = projectorPP := by
  ext x i; fin_cases i <;> simp [exteriorDegreeParity, Module.End.mul_apply]
theorem sheetParity_projectorPM : peirceSheetParity * projectorPM = projectorPM := by
  ext x i; fin_cases i <;> simp [peirceSheetParity_apply, Module.End.mul_apply]
theorem degreeParity_projectorPM : exteriorDegreeParity * projectorPM = -projectorPM := by
  ext x i; fin_cases i <;> simp [exteriorDegreeParity, Module.End.mul_apply]
theorem sheetParity_projectorMP : peirceSheetParity * projectorMP = -projectorMP := by
  ext x i; fin_cases i <;> simp [peirceSheetParity_apply, Module.End.mul_apply]
theorem degreeParity_projectorMP : exteriorDegreeParity * projectorMP = projectorMP := by
  ext x i; fin_cases i <;> simp [exteriorDegreeParity, Module.End.mul_apply]
theorem sheetParity_projectorMM : peirceSheetParity * projectorMM = -projectorMM := by
  ext x i; fin_cases i <;> simp [peirceSheetParity_apply, Module.End.mul_apply]
theorem degreeParity_projectorMM : exteriorDegreeParity * projectorMM = -projectorMM := by
  ext x i; fin_cases i <;> simp [exteriorDegreeParity, Module.End.mul_apply]

theorem nativeProjectorTrace_packet :
    (LinearMap.trace ℝ Carrier projectorPP, LinearMap.trace ℝ Carrier projectorPM,
      LinearMap.trace ℝ Carrier projectorMP, LinearMap.trace ℝ Carrier projectorMM) =
      (1, 3, 3, 1) := by
  simp only [linearMap_trace_eq_coordinateTrace]
  simp [InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.coordinateTrace,
    Fin.sum_univ_eight, Pi.single_apply]
  norm_num

end InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
