import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def symplecticContactEuler : FiveGradedCarrier D := genHscale D 1

theorem symplecticContactEuler_bracket (u : FiveGradedCarrier D) :
    ⁅symplecticContactEuler D, u⁆ =
      { minus2 := -2 * u.minus2, minus1 := -u.minus1,
        zero_symp := 0, zero_scale := 0,
        plus1 := u.plus1, plus2 := 2 * u.plus2 } := by
  apply FiveGradedCarrier.ext <;>
    simp [symplecticContactEuler, symplecticContact_lieBracket_eq,
      symplecticContactBracket, genHscale]

def SymplecticContactHasGrade (k : ℤ) (u : FiveGradedCarrier D) : Prop :=
  ⁅symplecticContactEuler D, u⁆ = (k : ℝ) • u

def symplecticContactGradeSpace (k : ℤ) :
    Submodule ℝ (FiveGradedCarrier D) where
  carrier := {u | SymplecticContactHasGrade D k u}
  zero_mem' := by
    change ⁅symplecticContactEuler D, (0 : FiveGradedCarrier D)⁆ =
      (k : ℝ) • (0 : FiveGradedCarrier D)
    simp
  add_mem' := by
    intro u v hu hv
    change SymplecticContactHasGrade D k (u + v)
    unfold SymplecticContactHasGrade at hu hv ⊢
    rw [lie_add, hu, hv, smul_add]
  smul_mem' := by
    intro c u hu
    change SymplecticContactHasGrade D k (c • u)
    unfold SymplecticContactHasGrade at hu ⊢
    rw [lie_smul, hu, smul_smul]
    module

@[simp] theorem mem_symplecticContactGradeSpace
    (k : ℤ) (u : FiveGradedCarrier D) :
    u ∈ symplecticContactGradeSpace D k ↔
      SymplecticContactHasGrade D k u := Iff.rfl

theorem symplecticContact_lie_mem_grade_add
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) := by
  change SymplecticContactHasGrade D k u at hu
  change SymplecticContactHasGrade D l v at hv
  change SymplecticContactHasGrade D (k + l) ⁅u, v⁆
  unfold SymplecticContactHasGrade at hu hv ⊢
  rw [leibniz_lie, hu, hv, smul_lie, lie_smul, ← add_smul]
  simp only [Int.cast_add]

theorem genEminus_contact_grade (a : ℝ) :
    genEminus D a ∈ symplecticContactGradeSpace D (-2) := by
  change SymplecticContactHasGrade D (-2) (genEminus D a)
  unfold SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;> simp [genEminus]

theorem injChargeMinus_contact_grade (x : FreudenthalCharge J) :
    injChargeMinus D x ∈ symplecticContactGradeSpace D (-1) := by
  change SymplecticContactHasGrade D (-1) (injChargeMinus D x)
  unfold SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;> simp [injChargeMinus]

theorem injChargePlus_contact_grade (x : FreudenthalCharge J) :
    injChargePlus D x ∈ symplecticContactGradeSpace D 1 := by
  change SymplecticContactHasGrade D 1 (injChargePlus D x)
  unfold SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;> simp [injChargePlus]

theorem genEplus_contact_grade (a : ℝ) :
    genEplus D a ∈ symplecticContactGradeSpace D 2 := by
  change SymplecticContactHasGrade D 2 (genEplus D a)
  unfold SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;> simp [genEplus]

end InfoGeometry.Exceptional.Freudenthal
