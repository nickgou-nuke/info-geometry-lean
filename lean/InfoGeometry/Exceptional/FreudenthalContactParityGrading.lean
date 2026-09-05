import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading
import InfoGeometry.Quantum.FiveGradedKramersModule

/-!
# Contact integer grading and derived parity

The corrected Freudenthal contact algebra already carries the native integer
weights `-2,-1,0,1,2`.  This file derives the compatible `ZMod 2` parity and
connects the abstract contact eigenspaces to the finite five-weight index used
by the complex Kramers module.

The parity is a quotient of the integer grading, not a replacement for it.
No grade-reversing automorphism of the Freudenthal carrier is assumed.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open InfoGeometry.Quantum.FiveGradedKramersModule

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Fermion parity derived from an integer contact degree. -/
def contactParity (k : ℤ) : ZMod 2 :=
  (k : ZMod 2)

@[simp] theorem contactParity_zero : contactParity 0 = 0 := rfl

@[simp] theorem contactParity_add (k l : ℤ) :
    contactParity (k + l) = contactParity k + contactParity l := by
  simp [contactParity]

@[simp] theorem contactParity_neg (k : ℤ) :
    contactParity (-k) = contactParity k := by
  change (-(k : ZMod 2)) = (k : ZMod 2)
  exact ZMod.neg_eq_self_mod_two _

/-- Contact grade space indexed by the finite five-weight type. -/
def finiteWeightGradeSpace (w : Weight) :
    Submodule ℝ (FiveGradedCarrier D) :=
  symplecticContactGradeSpace D w.value

@[simp] theorem mem_finiteWeightGradeSpace
    (w : Weight) (u : FiveGradedCarrier D) :
    u ∈ finiteWeightGradeSpace D w ↔
      ⁅symplecticContactEuler D, u⁆ = (w.value : ℝ) • u := Iff.rfl

/-- The bracket is simultaneously integer graded and parity graded. -/
theorem symplecticContact_lie_mem_multigrade
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l := by
  exact ⟨symplecticContact_lie_mem_grade_add D hu hv,
    contactParity_add k l⟩

/-- The five finite weight labels reproduce the named contact lanes. -/
theorem finite_weight_contact_packet :
    genEminus D 1 ∈ finiteWeightGradeSpace D Weight.minus2 ∧
      (∀ x, injChargeMinus D x ∈
        finiteWeightGradeSpace D Weight.minus1) ∧
      (∀ T, injSympZero D T ∈
        finiteWeightGradeSpace D Weight.zero) ∧
      genHscale D 1 ∈ finiteWeightGradeSpace D Weight.zero ∧
      (∀ x, injChargePlus D x ∈
        finiteWeightGradeSpace D Weight.plus1) ∧
      genEplus D 1 ∈ finiteWeightGradeSpace D Weight.plus2 := by
  exact ⟨genEminus_contact_grade D 1,
    injChargeMinus_contact_grade D,
    injSympZero_contact_grade D,
    genHscale_contact_grade D 1,
    injChargePlus_contact_grade D,
    genEplus_contact_grade D 1⟩

/-- Grade opposition leaves the derived parity unchanged. -/
theorem finiteWeight_opposite_same_contactParity (w : Weight) :
    contactParity w.opposite.value = contactParity w.value := by
  rw [Weight.value_opposite, contactParity_neg]

/-- Full contact `ℤ × ℤ₂` grading packet. -/
theorem contact_integer_parity_grading_packet
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) ∧
      contactParity (k + l) = contactParity k + contactParity l ∧
      contactParity (-k) = contactParity k := by
  exact ⟨symplecticContact_lie_mem_grade_add D hu hv,
    contactParity_add k l,
    contactParity_neg k⟩

end InfoGeometry.Exceptional.Freudenthal
