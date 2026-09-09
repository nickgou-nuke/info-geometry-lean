import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading
import InfoGeometry.Quantum.FiveGradedKramersModule

/-! The integer contact grading and its derived `ZMod 2` parity.
Parity is a quotient readout; it does not replace the integer grading.
-/
noncomputable section
namespace InfoGeometry.Exceptional.Freudenthal

open InfoGeometry.Quantum.FiveGradedKramersModule

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def contactParity (k : ℤ) : ZMod 2 := (k : ZMod 2)

@[simp] theorem contactParity_zero : contactParity 0 = 0 := rfl

@[simp] theorem contactParity_add (k l : ℤ) :
    contactParity (k + l) = contactParity k + contactParity l := by
  simp [contactParity]

@[simp] theorem contactParity_neg (k : ℤ) :
    contactParity (-k) = contactParity k := by
  unfold contactParity
  rw [Int.cast_neg]
  exact ZMod.neg_eq_self_mod_two _

def finiteWeightGradeSpace (w : Weight) :
    Submodule ℝ (FiveGradedCarrier D) :=
  symplecticContactGradeSpace D w.value

@[simp] theorem mem_finiteWeightGradeSpace
    (w : Weight) (u : FiveGradedCarrier D) :
    u ∈ finiteWeightGradeSpace D w ↔
      ⁅symplecticContactEuler D, u⁆ = (w.value : ℝ) • u := Iff.rfl

theorem symplecticContact_lie_mem_multigrade
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l := by
  exact ⟨symplecticContact_lie_mem_grade_add D hu hv, contactParity_add k l⟩

theorem finite_weight_contact_packet :
    genEminus D 1 ∈ finiteWeightGradeSpace D Weight.minus2 ∧
      (∀ x, injChargeMinus D x ∈ finiteWeightGradeSpace D Weight.minus1) ∧
      (∀ T, injSympZero D T ∈ finiteWeightGradeSpace D Weight.zero) ∧
      genHscale D 1 ∈ finiteWeightGradeSpace D Weight.zero ∧
      (∀ x, injChargePlus D x ∈ finiteWeightGradeSpace D Weight.plus1) ∧
      genEplus D 1 ∈ finiteWeightGradeSpace D Weight.plus2 := by
  have hzero (T : SymplecticTKKZero D) :
      injSympZero D T ∈ finiteWeightGradeSpace D Weight.zero := by
    change SymplecticContactHasGrade D 0 (injSympZero D T)
    unfold SymplecticContactHasGrade
    rw [symplecticContactEuler_bracket]
    apply FiveGradedCarrier.ext <;> simp [injSympZero]
  have hscale : genHscale D 1 ∈ finiteWeightGradeSpace D Weight.zero := by
    change SymplecticContactHasGrade D 0 (genHscale D 1)
    unfold SymplecticContactHasGrade
    rw [symplecticContactEuler_bracket]
    apply FiveGradedCarrier.ext <;> simp [genHscale]
  exact ⟨genEminus_contact_grade D 1,
    injChargeMinus_contact_grade D, hzero, hscale,
    injChargePlus_contact_grade D, genEplus_contact_grade D 1⟩

theorem finiteWeight_opposite_same_contactParity (w : Weight) :
    contactParity w.opposite.value = contactParity w.value := by
  rw [Weight.value_opposite, contactParity_neg]

theorem contact_integer_parity_grading_packet
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l ∧
      contactParity (-k) = contactParity k := by
  exact ⟨symplecticContact_lie_mem_grade_add D hu hv,
    contactParity_add k l, contactParity_neg k⟩

end InfoGeometry.Exceptional.Freudenthal
end noncomputable section
