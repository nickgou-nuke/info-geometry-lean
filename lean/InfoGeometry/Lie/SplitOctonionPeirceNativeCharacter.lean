import InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
open InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge

abbrev Carrier := PeirceCarrier
abbrev CarrierEnd := Module.End ℝ Carrier

@[simp] theorem peirceSheetParity_apply (x : Carrier) (i : Fin 8) :
    peirceSheetParity x i = if i.val < 4 then x i else -x i := by
  fin_cases i <;>
    simp [peirceSheetParity,
      InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge.peirceGrading]

@[simp] theorem exteriorDegreeParity_apply (x : Carrier) (i : Fin 8) :
    exteriorDegreeParity x i =
      if i.val = 0 then x i
      else if i.val < 5 then -x i
      else x i :=
  rfl

@[simp] theorem peirceCharacterProduct_apply (x : Carrier) (i : Fin 8) :
    peirceCharacterProduct x i =
      peirceSheetParity (exteriorDegreeParity x) i :=
  rfl

/-- Coordinate expression for the trace in the canonical `Fin 8` basis. -/
def coordinateTrace (T : CarrierEnd) : ℝ :=
  ∑ i : Fin 8, T (Pi.single i 1) i

/-- The coordinate expression is exactly Mathlib's native linear trace. -/
theorem linearMap_trace_eq_coordinateTrace (T : CarrierEnd) :
    LinearMap.trace ℝ Carrier T = coordinateTrace T := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 8))]
  simp [Matrix.trace, coordinateTrace]

theorem peirceSheetParity_sq_native :
    peirceSheetParity * peirceSheetParity = (1 : CarrierEnd) := by
  apply LinearMap.ext
  intro x
  exact peirceGrading_sq x

theorem peirceParities_commute :
    peirceSheetParity * exteriorDegreeParity =
      exteriorDegreeParity * peirceSheetParity := by
  apply LinearMap.ext
  intro x
  ext i
  fin_cases i <;>
    simp [peirceSheetParity, peirceGrading, exteriorDegreeParity,
      Module.End.mul_apply]

theorem peirceCharacterProduct_sq_native :
    peirceCharacterProduct * peirceCharacterProduct = (1 : CarrierEnd) := by
  unfold peirceCharacterProduct
  calc
    peirceSheetParity * exteriorDegreeParity *
        (peirceSheetParity * exteriorDegreeParity) =
      peirceSheetParity *
        (exteriorDegreeParity * peirceSheetParity) * exteriorDegreeParity := by
          simp only [mul_assoc]
    _ = peirceSheetParity *
        (peirceSheetParity * exteriorDegreeParity) * exteriorDegreeParity := by
          rw [peirceParities_commute]
    _ = (peirceSheetParity * peirceSheetParity) *
        (exteriorDegreeParity * exteriorDegreeParity) := by
          simp only [mul_assoc]
    _ = 1 := by
      rw [peirceSheetParity_sq_native, exteriorDegreeParity_sq, one_mul]

theorem peirceSheetParity_commutes_characterProduct :
    peirceSheetParity * peirceCharacterProduct =
      peirceCharacterProduct * peirceSheetParity := by
  unfold peirceCharacterProduct
  calc
    peirceSheetParity * (peirceSheetParity * exteriorDegreeParity) =
        (peirceSheetParity * peirceSheetParity) * exteriorDegreeParity := by
          rw [mul_assoc]
    _ = exteriorDegreeParity := by
          rw [peirceSheetParity_sq_native, one_mul]
    _ = (peirceSheetParity * exteriorDegreeParity) * peirceSheetParity := by
          calc
            exteriorDegreeParity = 1 * exteriorDegreeParity := by simp
            _ = (peirceSheetParity * peirceSheetParity) *
                exteriorDegreeParity := by
                  rw [peirceSheetParity_sq_native]
            _ = peirceSheetParity *
                (peirceSheetParity * exteriorDegreeParity) := by
                  rw [mul_assoc]
            _ = peirceSheetParity *
                (exteriorDegreeParity * peirceSheetParity) := by
                  rw [peirceParities_commute]
            _ = (peirceSheetParity * exteriorDegreeParity) *
                peirceSheetParity := by
                  rw [← mul_assoc]

theorem exteriorDegreeParity_commutes_characterProduct :
    exteriorDegreeParity * peirceCharacterProduct =
      peirceCharacterProduct * exteriorDegreeParity := by
  unfold peirceCharacterProduct
  rw [← mul_assoc, peirceParities_commute]

theorem coordinateTrace_identity : coordinateTrace (1 : CarrierEnd) = 8 := by
  simp [coordinateTrace]

theorem coordinateTrace_peirceSheetParity :
    coordinateTrace peirceSheetParity = 0 := by
  simp [coordinateTrace, peirceSheetParity, peirceGrading,
    Fin.sum_univ_eight, Pi.single_apply]

theorem coordinateTrace_exteriorDegreeParity :
    coordinateTrace exteriorDegreeParity = 0 := by
  simp [coordinateTrace, exteriorDegreeParity,
    Fin.sum_univ_eight]

theorem coordinateTrace_peirceCharacterProduct :
    coordinateTrace peirceCharacterProduct = -4 := by
  simp [coordinateTrace, peirceCharacterProduct, peirceSheetParity,
    peirceGrading, exteriorDegreeParity, Module.End.mul_apply,
    Fin.sum_univ_eight, Pi.single_apply]
  norm_num

theorem nativePeirceCharacter_packet :
    (LinearMap.trace ℝ Carrier (1 : CarrierEnd),
      LinearMap.trace ℝ Carrier peirceSheetParity,
      LinearMap.trace ℝ Carrier exteriorDegreeParity,
      LinearMap.trace ℝ Carrier peirceCharacterProduct) =
      (8, 0, 0, -4) := by
  simp only [linearMap_trace_eq_coordinateTrace]
  rw [coordinateTrace_identity, coordinateTrace_peirceSheetParity,
    coordinateTrace_exteriorDegreeParity,
    coordinateTrace_peirceCharacterProduct]

end InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter
