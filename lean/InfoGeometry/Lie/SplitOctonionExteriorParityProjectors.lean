import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exterior-parity projectors on the Peirce carrier

The Peirce carrier is only linearly identified with `Λ• ℝ³`; this file
packages the transported exterior `ℤ₂` grading as complementary projectors.
-/

namespace InfoGeometry.Lie.SplitOctonionExteriorParityProjectors

open InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

noncomputable section

abbrev PeirceCarrier :=
  InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter.Carrier
abbrev CarrierEnd := Module.End ℝ PeirceCarrier

def even : CarrierEnd := (1 / 2 : ℝ) • (1 + exteriorDegreeParity)
def odd : CarrierEnd := (1 / 2 : ℝ) • (1 - exteriorDegreeParity)

theorem even_sq : even * even = even := by
  dsimp [even]
  rw [smul_mul_smul]
  have h : (1 + exteriorDegreeParity) * (1 + exteriorDegreeParity) =
      (2 : ℝ) • (1 + exteriorDegreeParity) := by
    calc
      (1 + exteriorDegreeParity) * (1 + exteriorDegreeParity) =
          1 + exteriorDegreeParity + exteriorDegreeParity +
            exteriorDegreeParity * exteriorDegreeParity := by noncomm_ring
      _ = (2 : ℝ) • (1 + exteriorDegreeParity) := by
        rw [exteriorDegreeParity_sq]
        module
  rw [h, smul_smul]
  norm_num

theorem odd_sq : odd * odd = odd := by
  dsimp [odd]
  rw [smul_mul_smul]
  have h : (1 - exteriorDegreeParity) * (1 - exteriorDegreeParity) =
      (2 : ℝ) • (1 - exteriorDegreeParity) := by
    simp [sub_mul, mul_sub, exteriorDegreeParity_sq]
    module
  rw [h, smul_smul]
  norm_num

theorem even_mul_odd : even * odd = 0 := by
  dsimp [even, odd]
  rw [smul_mul_smul]
  have h : (1 + exteriorDegreeParity) * (1 - exteriorDegreeParity) = 0 := by
    simp [add_mul, mul_sub, exteriorDegreeParity_sq]
    abel
  rw [h, smul_zero]

theorem odd_mul_even : odd * even = 0 := by
  dsimp [odd, even]
  rw [smul_mul_smul]
  simp [sub_mul, mul_add, exteriorDegreeParity_sq]

theorem even_add_odd : even + odd = (1 : CarrierEnd) := by
  dsimp [even, odd]
  rw [smul_add, smul_sub]
  module

theorem even_eq_joint_projectors :
    even = projectorPP + projectorMP := by
  ext x i
  fin_cases i <;> simp [even, projectorPP, projectorMP,
    peirceCharacterProduct, Module.End.mul_apply]
  all_goals ring

theorem odd_eq_joint_projectors :
    odd = projectorPM + projectorMM := by
  ext x i
  fin_cases i <;> simp [odd, projectorPM, projectorMM,
    peirceCharacterProduct, Module.End.mul_apply]
  all_goals ring

end
end InfoGeometry.Lie.SplitOctonionExteriorParityProjectors
