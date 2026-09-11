import InfoGeometry.Exceptional.CyclotomicExceptionalGaloisActionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierDecomposition
import InfoGeometry.Exceptional.SymplecticOperatorConjugation
import InfoGeometry.OperatorAlgebra.GradeActionInterface
import InfoGeometry.Algebra.FiveGradedTKKSpec

/-!
# The cyclotomic action in the common grade-action interface

This is a projection readout of the existing `FiveGradedCarrier`.  It does
not introduce a second carrier or identify this exceptional representation
with the Clifford five-grading.  The two middle fields are deliberately kept
as the single grade-zero sector.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Galois

open InfoGeometry.Algebra
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.OperatorAlgebra

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def transportedZeroGradeAction
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (T : SymplecticTKKZero D) : SymplecticTKKZero D :=
  ⟨conjugateSymplecticOperator (rep.act g) T,
    conjugateSymplecticOperator_isSymplectic D (rep.act g)
      (rep.symplectic_invariant g) T T.property⟩

def actFiveGradedTransported
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) : FiveGradedCarrier D where
  minus2 := u.minus2
  minus1 := rep.act g u.minus1
  zero_symp := transportedZeroGradeAction D rep g u.zero_symp
  zero_scale := u.zero_scale
  plus1 := rep.act g u.plus1
  plus2 := u.plus2

@[simp] theorem actFiveGradedTransported_zero_symp
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g u).zero_symp =
      transportedZeroGradeAction D rep g u.zero_symp := rfl

theorem transportedZeroGradeAction_mul
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g h : (ZMod N)ˣ) (T : SymplecticTKKZero D) :
    transportedZeroGradeAction D rep (g * h) T =
      transportedZeroGradeAction D rep g
        (transportedZeroGradeAction D rep h T) := by
  apply Subtype.ext
  change conjugateSymplecticOperator (rep.act (g * h)) T =
    conjugateSymplecticOperator (rep.act g)
      (conjugateSymplecticOperator (rep.act h) T)
  rw [rep.act_mul]
  apply LinearMap.ext
  intro x
  simp [conjugateSymplecticOperator, LinearMap.comp_apply]

theorem transportedZeroGradeAction_apply
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    ((transportedZeroGradeAction D rep g T :
      Module.End ℝ (FreudenthalCharge J)) (rep.act g x)) =
      rep.act g ((T : Module.End ℝ (FreudenthalCharge J)) x) := by
  simp [transportedZeroGradeAction, conjugateSymplecticOperator,
    LinearMap.comp_apply]

theorem actFiveGradedTransported_bracket_zero_symp
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g (fiveGradedBracket D u v)).zero_symp =
      (fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v)).zero_symp := by
  apply Subtype.ext
  simp only [actFiveGradedTransported, fiveGradedBracket,
    transportedZeroGradeAction]
  change conjugateSymplecticOperator (rep.act g)
      ((⁅(u.zero_symp : Module.End ℝ (FreudenthalCharge J)),
          (v.zero_symp : Module.End ℝ (FreudenthalCharge J))⁆ :
        Module.End ℝ (FreudenthalCharge J)) +
        mixedSymplecticBracket D u.minus1 v.plus1 -
        mixedSymplecticBracket D v.minus1 u.plus1) = _
  rw [InfoGeometry.Exceptional.Freudenthal.conjugateSymplecticOperator_sub,
    InfoGeometry.Exceptional.Freudenthal.conjugateSymplecticOperator_add,
    InfoGeometry.Exceptional.Freudenthal.conjugateSymplecticOperator_zeroBracket,
    InfoGeometry.Exceptional.Freudenthal.conjugate_mixedSymplecticBracket,
    InfoGeometry.Exceptional.Freudenthal.conjugate_mixedSymplecticBracket]
  rfl

theorem actFiveGradedTransported_bracket_minus2
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g (fiveGradedBracket D u v)).minus2 =
      (fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v)).minus2 := by
  simp only [actFiveGradedTransported, fiveGradedBracket]
  rw [rep.symplectic_invariant]

theorem actFiveGradedTransported_bracket_zero_scale
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g (fiveGradedBracket D u v)).zero_scale =
      (fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v)).zero_scale := by
  simp only [actFiveGradedTransported, fiveGradedBracket]
  rw [rep.symplectic_invariant, rep.symplectic_invariant]

theorem actFiveGradedTransported_bracket_plus2
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g (fiveGradedBracket D u v)).plus2 =
      (fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v)).plus2 := by
  simp only [actFiveGradedTransported, fiveGradedBracket]
  rw [rep.symplectic_invariant]

theorem actFiveGradedTransported_bracket_minus1
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g (fiveGradedBracket D u v)).minus1 =
      (fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v)).minus1 := by
  simp [actFiveGradedTransported, fiveGradedBracket,
    transportedZeroGradeAction_apply]

theorem actFiveGradedTransported_bracket_plus1
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    (actFiveGradedTransported D rep g (fiveGradedBracket D u v)).plus1 =
      (fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v)).plus1 := by
  simp [actFiveGradedTransported, fiveGradedBracket,
    transportedZeroGradeAction_apply]

theorem actFiveGradedTransported_bracket
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u v : FiveGradedCarrier D) :
    actFiveGradedTransported D rep g (fiveGradedBracket D u v) =
      fiveGradedBracket D
        (actFiveGradedTransported D rep g u)
        (actFiveGradedTransported D rep g v) := by
  apply FiveGradedCarrier.ext
  · exact actFiveGradedTransported_bracket_minus2 D rep g u v
  · exact actFiveGradedTransported_bracket_minus1 D rep g u v
  · exact actFiveGradedTransported_bracket_zero_symp D rep g u v
  · exact actFiveGradedTransported_bracket_zero_scale D rep g u v
  · exact actFiveGradedTransported_bracket_plus1 D rep g u v
  · exact actFiveGradedTransported_bracket_plus2 D rep g u v

theorem actFiveGradedTransported_decomposition
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    actFiveGradedTransported D rep g u =
      genEminus D u.minus2 + injChargeMinus D (rep.act g u.minus1) +
        injSympZero D (transportedZeroGradeAction D rep g u.zero_symp) +
        genHscale D u.zero_scale +
        injChargePlus D (rep.act g u.plus1) + genEplus D u.plus2 := by
  apply FiveGradedCarrier.ext <;>
    simp [actFiveGradedTransported, genEminus, injChargeMinus,
      injSympZero, genHscale, injChargePlus, genEplus,
      FiveGradedCarrier.instAdd]

theorem actFiveGradedTransported_one
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (u : FiveGradedCarrier D) :
    actFiveGradedTransported D rep 1 u = u := by
  apply FiveGradedCarrier.ext
  · rfl
  · simpa using congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f u.minus1)
      (rep.act_one)
  · apply Subtype.ext
    change (rep.act 1).toLinearMap.comp
        ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)).comp
          (rep.act 1).symm.toLinearMap) = u.zero_symp
    rw [rep.act_one]
    rfl
  · rfl
  · simpa using congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f u.plus1)
      (rep.act_one)
  · rfl

theorem actFiveGradedTransported_mul
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g h : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    actFiveGradedTransported D rep (g * h) u =
      actFiveGradedTransported D rep g
        (actFiveGradedTransported D rep h u) := by
  apply FiveGradedCarrier.ext
  · rfl

  · simpa [actFiveGradedTransported] using
      congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f u.minus1)
        (rep.act_mul g h)
  · apply Subtype.ext
    exact congrArg Subtype.val
      (transportedZeroGradeAction_mul D rep g h u.zero_symp)
  · rfl
  · simpa [actFiveGradedTransported] using
      congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f u.plus1)
        (rep.act_mul g h)
  · rfl

theorem actFiveGradedTransported_inv
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    actFiveGradedTransported D rep g⁻¹
        (actFiveGradedTransported D rep g u) = u := by
  calc
    actFiveGradedTransported D rep g⁻¹
        (actFiveGradedTransported D rep g u) =
        actFiveGradedTransported D rep (g⁻¹ * g) u := by
          symm
          exact actFiveGradedTransported_mul D rep g⁻¹ g u
    _ = actFiveGradedTransported D rep 1 u := by rw [inv_mul_cancel]
    _ = u := actFiveGradedTransported_one D rep u

def actFiveGradedTransportedEquiv
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) : FiveGradedCarrier D ≃ FiveGradedCarrier D where
  toFun := actFiveGradedTransported D rep g
  invFun := actFiveGradedTransported D rep g⁻¹
  left_inv u := actFiveGradedTransported_inv D rep g u
  right_inv u := by
    calc
      actFiveGradedTransported D rep g
          (actFiveGradedTransported D rep g⁻¹ u) =
        actFiveGradedTransported D rep (g * g⁻¹) u := by
          symm
          exact actFiveGradedTransported_mul D rep g g⁻¹ u
      _ = actFiveGradedTransported D rep 1 u := by rw [mul_inv_cancel]
      _ = u := actFiveGradedTransported_one D rep u

theorem transportedZeroGradeAction_zero
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) :
    transportedZeroGradeAction D rep g (0 : SymplecticTKKZero D) = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  simp [transportedZeroGradeAction, conjugateSymplecticOperator,
    LinearMap.comp_apply]

/-- Membership in one of the five native sectors of `FiveGradedCarrier`. -/
def fiveGradedCarrierSector (g : TKKGrade) : Set (FiveGradedCarrier D) :=
  {u | match g with
    | TKKGrade.m2 => u.minus1 = 0 ∧ u.zero_symp = 0 ∧ u.zero_scale = 0 ∧
        u.plus1 = 0 ∧ u.plus2 = 0
    | TKKGrade.m1 => u.minus2 = 0 ∧ u.zero_symp = 0 ∧ u.zero_scale = 0 ∧
        u.plus1 = 0 ∧ u.plus2 = 0
    | TKKGrade.z0 => u.minus2 = 0 ∧ u.minus1 = 0 ∧
        u.plus1 = 0 ∧ u.plus2 = 0
    | TKKGrade.p1 => u.minus2 = 0 ∧ u.minus1 = 0 ∧ u.zero_symp = 0 ∧
        u.zero_scale = 0 ∧ u.plus2 = 0
    | TKKGrade.p2 => u.minus2 = 0 ∧ u.minus1 = 0 ∧ u.zero_symp = 0 ∧
        u.zero_scale = 0 ∧ u.plus1 = 0 }

theorem actFiveGraded_mapsTo_sector
    (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (k : TKKGrade) :
    Set.MapsTo (CyclotomicSymplecticRepresentation.actFiveGraded D rep g)
      (fiveGradedCarrierSector D k) (fiveGradedCarrierSector D k) := by
  intro u hu
  cases k <;> simp only [fiveGradedCarrierSector, Set.mem_setOf_eq] at hu ⊢
  · exact ⟨by simpa using hu.1, by simpa using hu.2.1, by simpa using hu.2.2.1,
      by simpa using hu.2.2.2.1, by simpa using hu.2.2.2.2⟩
  · exact ⟨by simpa using hu.1, by simpa using hu.2.1, by simpa using hu.2.2.1,
      by simpa using hu.2.2.2.1, by simpa using hu.2.2.2.2⟩
  · exact ⟨by simpa using hu.1, by simpa using hu.2.1, by simpa using hu.2.2.1,
      by simpa using hu.2.2.2⟩
  · exact ⟨by simpa using hu.1, by simpa using hu.2.1, by simpa using hu.2.2.1,
      by simpa using hu.2.2.2.1, by simpa using hu.2.2.2.2⟩
  · exact ⟨by simpa using hu.1, by simpa using hu.2.1, by simpa using hu.2.2.1,
      by simpa using hu.2.2.2.1, by simpa using hu.2.2.2.2⟩

theorem actFiveGraded_mapsTo_grade
    (rep : CyclotomicSymplecticRepresentation N D) :
    MapsToGrade (fiveGradedCarrierSector D)
      (CyclotomicSymplecticRepresentation.actFiveGraded D rep)
      (fun _ k => k) := by
  intro g k u hu
  exact actFiveGraded_mapsTo_sector D rep g k hu

theorem actFiveGradedTransported_mapsTo_sector
    (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (k : TKKGrade) :
    Set.MapsTo (actFiveGradedTransported D rep g)
      (fiveGradedCarrierSector D k) (fiveGradedCarrierSector D k) := by
  intro u hu
  cases k <;> simp only [fiveGradedCarrierSector, Set.mem_setOf_eq] at hu ⊢
  · exact ⟨by simpa [actFiveGradedTransported] using hu.1,
      by simpa [actFiveGradedTransported, hu.2.1] using
        transportedZeroGradeAction_zero D rep g,
      by simpa [actFiveGradedTransported] using hu.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2.2⟩
  · exact ⟨by simpa [actFiveGradedTransported] using hu.1,
      by simpa [actFiveGradedTransported, hu.2.1] using
        transportedZeroGradeAction_zero D rep g,
      by simpa [actFiveGradedTransported] using hu.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2.2⟩
  · exact ⟨by simpa [actFiveGradedTransported] using hu.1,
      by simpa [actFiveGradedTransported] using hu.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2⟩
  · exact ⟨by simpa [actFiveGradedTransported] using hu.1,
      by simpa [actFiveGradedTransported] using hu.2.1,
      by simpa [actFiveGradedTransported, hu.2.2.1] using
        transportedZeroGradeAction_zero D rep g,
      by simpa [actFiveGradedTransported] using hu.2.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2.2⟩
  · exact ⟨by simpa [actFiveGradedTransported] using hu.1,
      by simpa [actFiveGradedTransported] using hu.2.1,
      by simpa [actFiveGradedTransported, hu.2.2.1] using
        transportedZeroGradeAction_zero D rep g,
      by simpa [actFiveGradedTransported] using hu.2.2.2.1,
      by simpa [actFiveGradedTransported] using hu.2.2.2.2⟩

theorem actFiveGradedTransported_mapsTo_grade
    (rep : CyclotomicSymplecticRepresentation N D) :
    MapsToGrade (fiveGradedCarrierSector D)
      (actFiveGradedTransported D rep)
      (fun _ k => k) := by
  intro g k u hu
  exact actFiveGradedTransported_mapsTo_sector D rep g k hu

theorem actFiveGradedTransportedEquiv_sector_image_eq
    {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (k : TKKGrade) :
    actFiveGradedTransportedEquiv D rep g '' fiveGradedCarrierSector D k =
      fiveGradedCarrierSector D k := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact actFiveGradedTransported_mapsTo_sector D rep g k hx
  · intro y hy
    have hy' := actFiveGradedTransported_mapsTo_sector D rep g⁻¹ k hy
    refine ⟨actFiveGradedTransported D rep g⁻¹ y, hy', ?_⟩
    change actFiveGradedTransported D rep g
      (actFiveGradedTransported D rep g⁻¹ y) = y
    calc
      actFiveGradedTransported D rep g
          (actFiveGradedTransported D rep g⁻¹ y) =
        actFiveGradedTransported D rep (g * g⁻¹) y := by
          symm
          exact actFiveGradedTransported_mul D rep g g⁻¹ y
      _ = actFiveGradedTransported D rep 1 y := by rw [mul_inv_cancel]
      _ = y := actFiveGradedTransported_one D rep y

theorem actFiveGraded_decomposition
    (rep : CyclotomicSymplecticRepresentation N D)
    (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    CyclotomicSymplecticRepresentation.actFiveGraded D rep g u =
      genEminus D u.minus2 + injChargeMinus D (rep.act g u.minus1) +
      injSympZero D u.zero_symp + genHscale D u.zero_scale +
        injChargePlus D (rep.act g u.plus1) + genEplus D u.plus2 := by
  apply FiveGradedCarrier.ext <;>
    simp [CyclotomicSymplecticRepresentation.actFiveGraded,
      genEminus, injChargeMinus, injSympZero, genHscale,
      injChargePlus, genEplus, FiveGradedCarrier.instAdd]

end InfoGeometry.Exceptional.Galois
