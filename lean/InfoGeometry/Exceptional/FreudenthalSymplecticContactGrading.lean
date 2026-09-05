import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra

/-!
# Native five-grading of the corrected symplectic contact Lie algebra

The Euler element `H` acts diagonally with weights `-2,-1,0,1,2`.  The
corresponding adjoint eigenspaces are bundled as Mathlib submodules and their
Lie brackets add weights.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Euler element of the contact grading. -/
def symplecticContactEuler : FiveGradedCarrier D :=
  genHscale D 1

/-- Explicit diagonal adjoint action of the Euler element. -/
theorem symplecticContactEuler_bracket
    (u : FiveGradedCarrier D) :
    ⁅symplecticContactEuler D, u⁆ =
      { minus2 := -2 * u.minus2
        minus1 := -u.minus1
        zero_symp := 0
        zero_scale := 0
        plus1 := u.plus1
        plus2 := 2 * u.plus2 } := by
  apply FiveGradedCarrier.ext <;>
    simp [symplecticContactEuler, symplecticContact_lieBracket_eq,
      symplecticContactBracket, genHscale]

/-- Adjoint grade predicate. -/
def SymplecticContactHasGrade
    (k : ℤ) (u : FiveGradedCarrier D) : Prop :=
  ⁅symplecticContactEuler D, u⁆ = (k : ℝ) • u

/-- Grade-`k` adjoint eigenspace. -/
def symplecticContactGradeSpace (k : ℤ) :
    Submodule ℝ (FiveGradedCarrier D) where
  carrier := {u | SymplecticContactHasGrade D k u}
  zero_mem' := by
    simp [SymplecticContactHasGrade]
  add_mem' := by
    intro u v hu hv
    unfold SymplecticContactHasGrade at hu hv ⊢
    rw [lie_add, hu, hv, smul_add]
  smul_mem' := by
    intro c u hu
    unfold SymplecticContactHasGrade at hu ⊢
    rw [lie_smul, hu, smul_smul]
    ring_nf

@[simp] theorem mem_symplecticContactGradeSpace
    (k : ℤ) (u : FiveGradedCarrier D) :
    u ∈ symplecticContactGradeSpace D k ↔
      SymplecticContactHasGrade D k u := Iff.rfl

/-- Native Lie brackets add contact grades. -/
theorem symplecticContact_lie_mem_grade_add
    {k l : ℤ} {u v : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k)
    (hv : v ∈ symplecticContactGradeSpace D l) :
    ⁅u, v⁆ ∈ symplecticContactGradeSpace D (k + l) := by
  unfold SymplecticContactHasGrade at hu hv ⊢
  rw [leibniz_lie, hu, hv, smul_lie, lie_smul, ← add_smul]
  simp only [Int.cast_add]

/-- Bilinear bracket map between two fixed grades. -/
def symplecticContactGradeBracket (k l : ℤ) :
    symplecticContactGradeSpace D k →ₗ[ℝ]
      symplecticContactGradeSpace D l →ₗ[ℝ]
        symplecticContactGradeSpace D (k + l) :=
  LinearMap.mk₂ ℝ
    (fun u v => ⟨⁅u.1, v.1⁆,
      symplecticContact_lie_mem_grade_add D u.2 v.2⟩)
    (fun u₁ u₂ v => by
      apply Subtype.ext
      simp)
    (fun c u v => by
      apply Subtype.ext
      simp)
    (fun u v₁ v₂ => by
      apply Subtype.ext
      simp)
    (fun c u v => by
      apply Subtype.ext
      simp)

/-- Extreme negative generator has grade `-2`. -/
theorem genEminus_contact_grade
    (a : ℝ) :
    genEminus D a ∈ symplecticContactGradeSpace D (-2) := by
  unfold symplecticContactGradeSpace SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;>
    simp [genEminus]

/-- Negative charge generator has grade `-1`. -/
theorem injChargeMinus_contact_grade
    (x : FreudenthalCharge J) :
    injChargeMinus D x ∈ symplecticContactGradeSpace D (-1) := by
  unfold symplecticContactGradeSpace SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;>
    simp [injChargeMinus]

/-- Zero-grade symplectic generators have grade zero. -/
theorem injSympZero_contact_grade
    (T : SymplecticTKKZero D) :
    injSympZero D T ∈ symplecticContactGradeSpace D 0 := by
  unfold symplecticContactGradeSpace SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;>
    simp [injSympZero]

/-- Euler multiples have grade zero. -/
theorem genHscale_contact_grade
    (h : ℝ) :
    genHscale D h ∈ symplecticContactGradeSpace D 0 := by
  unfold symplecticContactGradeSpace SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;>
    simp [genHscale]

/-- Positive charge generator has grade `+1`. -/
theorem injChargePlus_contact_grade
    (x : FreudenthalCharge J) :
    injChargePlus D x ∈ symplecticContactGradeSpace D 1 := by
  unfold symplecticContactGradeSpace SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;>
    simp [injChargePlus]

/-- Extreme positive generator has grade `+2`. -/
theorem genEplus_contact_grade
    (a : ℝ) :
    genEplus D a ∈ symplecticContactGradeSpace D 2 := by
  unfold symplecticContactGradeSpace SymplecticContactHasGrade
  rw [symplecticContactEuler_bracket]
  apply FiveGradedCarrier.ext <;>
    simp [genEplus]

/-- The extreme generators retain the canonical `sl2` relation. -/
theorem symplecticContact_extreme_bracket :
    ⁅genEplus D 1, genEminus D 1⁆ = symplecticContactEuler D := by
  apply FiveGradedCarrier.ext <;>
    simp [symplecticContactEuler, symplecticContact_lieBracket_eq,
      symplecticContactBracket, genEplus, genEminus, genHscale]

/-- Exact same-sign Heisenberg relations, including the forced negative-side
sign. -/
theorem symplecticContact_minus1_minus1
    (x y : FreudenthalCharge J) :
    ⁅injChargeMinus D x, injChargeMinus D y⁆ =
      genEminus D
        (-2 * FreudenthalCharge.symplecticForm D x y) :=
  corrected_minus1_minus1_bracket D x y

theorem symplecticContact_plus1_plus1
    (x y : FreudenthalCharge J) :
    ⁅injChargePlus D x, injChargePlus D y⁆ =
      genEplus D
        (2 * FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    simp [symplecticContact_lieBracket_eq, symplecticContactBracket,
      injChargePlus, genEplus]

/-- Named five-grade packet. -/
theorem symplectic_contact_five_grade_packet :
    genEminus D 1 ∈ symplecticContactGradeSpace D (-2) ∧
      (∀ x, injChargeMinus D x ∈
        symplecticContactGradeSpace D (-1)) ∧
      (∀ T, injSympZero D T ∈ symplecticContactGradeSpace D 0) ∧
      (∀ x, injChargePlus D x ∈
        symplecticContactGradeSpace D 1) ∧
      genEplus D 1 ∈ symplecticContactGradeSpace D 2 ∧
      ⁅genEplus D 1, genEminus D 1⁆ = symplecticContactEuler D := by
  exact ⟨genEminus_contact_grade D 1,
    injChargeMinus_contact_grade D,
    injSympZero_contact_grade D,
    injChargePlus_contact_grade D,
    genEplus_contact_grade D 1,
    symplecticContact_extreme_bracket D⟩

end InfoGeometry.Exceptional.Freudenthal
