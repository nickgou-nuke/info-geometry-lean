import InfoGeometry.Canonical.CanonicalZornCompositionTriality

noncomputable section

namespace CanonicalZornCompositionTriality

open InfoGeometry.Physics.SplitOctonionBraidSU3

theorem trialityForm_add_vector (first second : Vector8) (positive : SpinorPlus8)
    (negative : SpinorMinus8) :
    trialityForm (first + second) positive negative =
      trialityForm first positive negative + trialityForm second positive negative := by
  simp only [trialityForm, zornCopy_add_val]
  simp [zornTrace, zornMul, zornAdd, dot3, cross3]
  ring

theorem trialityForm_smul_vector (scalar : ℂ) (vector : Vector8) (positive : SpinorPlus8)
    (negative : SpinorMinus8) :
    trialityForm (scalar • vector) positive negative = scalar * trialityForm vector positive negative := by
  simp only [trialityForm, zornCopy_smul_val]
  simp [zornTrace, zornMul, coordinatesToZorn, zornCoordinates, dot3, cross3, smul_eq_mul]
  ring

theorem trialityForm_add_positive (vector : Vector8) (first second : SpinorPlus8)
    (negative : SpinorMinus8) :
    trialityForm vector (first + second) negative =
      trialityForm vector first negative + trialityForm vector second negative := by
  simp only [trialityForm, zornCopy_add_val]
  simp [zornTrace, zornMul, zornAdd, dot3, cross3]
  ring

theorem trialityForm_smul_positive (scalar : ℂ) (vector : Vector8) (positive : SpinorPlus8)
    (negative : SpinorMinus8) :
    trialityForm vector (scalar • positive) negative = scalar * trialityForm vector positive negative := by
  simp only [trialityForm, zornCopy_smul_val]
  simp [zornTrace, zornMul, coordinatesToZorn, zornCoordinates, dot3, cross3, smul_eq_mul]
  ring

theorem trialityForm_add_negative (vector : Vector8) (positive : SpinorPlus8)
    (first second : SpinorMinus8) :
    trialityForm vector positive (first + second) =
      trialityForm vector positive first + trialityForm vector positive second := by
  simp only [trialityForm, zornCopy_add_val]
  simp [zornTrace, zornMul, zornAdd, dot3, cross3]
  ring

theorem trialityForm_smul_negative (scalar : ℂ) (vector : Vector8) (positive : SpinorPlus8)
    (negative : SpinorMinus8) :
    trialityForm vector positive (scalar • negative) = scalar * trialityForm vector positive negative := by
  simp only [trialityForm, zornCopy_smul_val]
  simp [zornTrace, zornMul, coordinatesToZorn, zornCoordinates, dot3, cross3, smul_eq_mul]
  ring

def trialityTrilinear : Vector8 →ₗ[ℂ] SpinorPlus8 →ₗ[ℂ] SpinorMinus8 →ₗ[ℂ] ℂ where
  toFun vector := {
    toFun positive := {
      toFun := trialityForm vector positive
      map_add' := trialityForm_add_negative vector positive
      map_smul' scalar negative := trialityForm_smul_negative scalar vector positive negative }
    map_add' first second := by ext negative; exact trialityForm_add_positive vector first second negative
    map_smul' scalar positive := by ext negative; exact trialityForm_smul_positive scalar vector positive negative }
  map_add' first second := by ext positive negative; exact trialityForm_add_vector first second positive negative
  map_smul' scalar vector := by ext positive negative; exact trialityForm_smul_vector scalar vector positive negative

theorem trialityTrilinear_cubic_phase (phase : ℂ) (hphase : phase ^ 3 = 1)
    (vector : Vector8) (positive : SpinorPlus8) (negative : SpinorMinus8) :
    trialityTrilinear (phase • vector) (phase • positive) (phase • negative) =
      trialityTrilinear vector positive negative := by
  change trialityForm (phase • vector) (phase • positive) (phase • negative) = _
  rw [trialityForm_smul_vector, trialityForm_smul_positive, trialityForm_smul_negative]
  change phase * (phase * (phase * trialityForm vector positive negative)) =
    trialityForm vector positive negative
  calc
    _ = phase ^ 3 * trialityForm vector positive negative := by ring
    _ = _ := by rw [hphase, one_mul]

end CanonicalZornCompositionTriality
