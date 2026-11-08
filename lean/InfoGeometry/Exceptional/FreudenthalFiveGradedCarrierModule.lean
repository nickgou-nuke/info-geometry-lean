import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierAddGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

noncomputable instance : Module ℝ (FiveGradedCarrier D) where
  one_smul u := by
    apply FiveGradedCarrier.ext <;>
      simp only [FiveGradedCarrier.smul_minus2, FiveGradedCarrier.smul_minus1,
        FiveGradedCarrier.smul_zero_symp, FiveGradedCarrier.smul_zero_scale,
        FiveGradedCarrier.smul_plus1, FiveGradedCarrier.smul_plus2,
        one_mul, one_smul]
  mul_smul r s u := by
    apply FiveGradedCarrier.ext <;>
      simp only [FiveGradedCarrier.smul_minus2, FiveGradedCarrier.smul_minus1,
        FiveGradedCarrier.smul_zero_symp, FiveGradedCarrier.smul_zero_scale,
        FiveGradedCarrier.smul_plus1, FiveGradedCarrier.smul_plus2,
        mul_assoc, mul_smul]
  smul_zero r := by
    change (⟨r * 0, r • (0 : FreudenthalCharge J),
      r • (0 : SymplecticTKKZero D), r * 0,
      r • (0 : FreudenthalCharge J), r * 0⟩ : FiveGradedCarrier D) = 0
    congr <;> simp
  smul_add r u v := by
    apply FiveGradedCarrier.ext <;>
      simp only [FiveGradedCarrier.smul_minus2, FiveGradedCarrier.smul_minus1,
        FiveGradedCarrier.smul_zero_symp, FiveGradedCarrier.smul_zero_scale,
        FiveGradedCarrier.smul_plus1, FiveGradedCarrier.smul_plus2,
        FiveGradedCarrier.add_minus2, FiveGradedCarrier.add_minus1,
        FiveGradedCarrier.add_zero_symp, FiveGradedCarrier.add_zero_scale,
        FiveGradedCarrier.add_plus1, FiveGradedCarrier.add_plus2,
        mul_add, smul_add]
  add_smul r s u := by
    apply FiveGradedCarrier.ext
    · simp [FiveGradedCarrier.smul_minus2, add_mul]
    · simp [FiveGradedCarrier.smul_minus1, add_smul]
    · simp [FiveGradedCarrier.smul_zero_symp, add_smul]
    · simp [FiveGradedCarrier.smul_zero_scale, add_mul]
    · simp [FiveGradedCarrier.smul_plus1, add_smul]
    · simp [FiveGradedCarrier.smul_plus2, add_mul]
  zero_smul u := by
    change (⟨0 * u.minus2, (0 : ℝ) • u.minus1,
      (0 : ℝ) • u.zero_symp, 0 * u.zero_scale,
      (0 : ℝ) • u.plus1, 0 * u.plus2⟩ : FiveGradedCarrier D) = 0
    congr <;> simp

end InfoGeometry.Exceptional.Freudenthal
