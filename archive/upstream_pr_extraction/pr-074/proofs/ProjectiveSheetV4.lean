import proofs.KleinBottleSixfoldCyclotomic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The projective Klein-four sheet quotient

The two anticommuting sheet involutions generate an eight-element Pin shadow.
Its native finite model is `DihedralGroup 4`: adjacent reflections square to
one and their product is a quarter-turn.  The half-turn is the central scalar
sign.  Reduction of rotation indices modulo two constructs the actual quotient
and identifies it with `DihedralGroup 2`, for which Mathlib supplies the
`IsKleinFour` instance.
-/

namespace ProjectiveSheetV4

abbrev SheetPinExtension := DihedralGroup 4
abbrev SheetProjectiveV4 := DihedralGroup 2

def pinJ : SheetPinExtension := DihedralGroup.sr 0
def pinGamma : SheetPinExtension := DihedralGroup.sr 1
def centralSign : SheetPinExtension := DihedralGroup.r 2

@[simp] theorem pinJ_sq : pinJ * pinJ = 1 := by simp [pinJ]
@[simp] theorem pinGamma_sq : pinGamma * pinGamma = 1 := by simp [pinGamma]
@[simp] theorem centralSign_sq : centralSign * centralSign = 1 := by
  simp only [centralSign, DihedralGroup.r_mul_r]
  rw [show (2 : ZMod 4) + 2 = 0 by decide, DihedralGroup.r_zero]

theorem centralSign_commutes (g : SheetPinExtension) :
    centralSign * g = g * centralSign := by
  cases g with
  | r i =>
      simp [centralSign, add_comm]
  | sr i =>
      simp only [centralSign, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      rw [sub_eq_add_neg, show -(2 : ZMod 4) = 2 by decide, add_comm]

/-- Adjacent reflections anticommute up to the central half-turn. -/
theorem pin_anticommutation :
    pinJ * pinGamma = centralSign * (pinGamma * pinJ) := by
  simp only [pinJ, pinGamma, centralSign, DihedralGroup.sr_mul_sr,
    DihedralGroup.r_mul_r]
  congr 1

/-- Reduction modulo two kills the central half-turn. -/
def projectivize : SheetPinExtension →* SheetProjectiveV4 where
  toFun
    | DihedralGroup.r i => DihedralGroup.r (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) i)
    | DihedralGroup.sr i => DihedralGroup.sr (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) i)
  map_one' := rfl
  map_mul' := by
    intro g h
    cases g <;> cases h <;>
      simp [ZMod.castHom_apply, map_add, map_sub]

theorem projectivize_surjective : Function.Surjective projectivize := by
  intro g
  cases g with
  | r i =>
      obtain ⟨j, hj⟩ := ZMod.castHom_surjective (by norm_num : 2 ∣ 4) i
      refine ⟨DihedralGroup.r j, ?_⟩
      exact congrArg DihedralGroup.r hj
  | sr i =>
      obtain ⟨j, hj⟩ := ZMod.castHom_surjective (by norm_num : 2 ∣ 4) i
      refine ⟨DihedralGroup.sr j, ?_⟩
      exact congrArg DihedralGroup.sr hj

@[simp] theorem centralSign_in_kernel : centralSign ∈ projectivize.ker := by
  change DihedralGroup.r ((ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) 2) = 1
  rw [show (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) 2 = 0 by decide]
  exact DihedralGroup.r_zero

/-- The literal two-element scalar-sign subgroup `{1,z}`. -/
def centralSignSubgroup : Subgroup SheetPinExtension where
  carrier := {g | g = 1 ∨ g = centralSign}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul centralSign)
    · exact Or.inr (mul_one centralSign)
    · exact Or.inl centralSign_sq
  inv_mem' := by
    intro a ha
    rcases ha with (rfl | rfl)
    · exact Or.inl inv_one
    · apply Or.inr
      calc
        centralSign⁻¹ = centralSign⁻¹ * (centralSign * centralSign) := by
          rw [centralSign_sq, mul_one]
        _ = (centralSign⁻¹ * centralSign) * centralSign := by rw [mul_assoc]
        _ = centralSign := by rw [inv_mul_cancel, one_mul]

@[simp] theorem mem_centralSignSubgroup_iff (g : SheetPinExtension) :
    g ∈ centralSignSubgroup ↔ g = 1 ∨ g = centralSign :=
  Iff.rfl

/-- The abstract kernel is exactly the central scalar subgroup, not merely a
subgroup containing the half-turn. -/
theorem cast_mod_two_eq_zero_iff (i : ZMod 4) :
    (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) i = 0 ↔ i = 0 ∨ i = 2 := by
  rw [ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hi : i.val < 4 := i.val_lt
    have hcases : i.val = 0 ∨ i.val = 2 := by omega
    rcases hcases with h0 | h2
    · left
      apply ZMod.val_injective 4
      simpa [ZMod.val] using h0
    · right
      apply ZMod.val_injective 4
      simpa [ZMod.val] using h2
  · rintro (rfl | rfl) <;> norm_num [ZMod.val]

theorem projectivize_kernel_eq_centralSign :
    projectivize.ker = centralSignSubgroup := by
  ext g
  cases g with
  | r i =>
      change DihedralGroup.r ((ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) i) =
          DihedralGroup.r 0 ↔ DihedralGroup.r i = DihedralGroup.r 0 ∨
            DihedralGroup.r i = DihedralGroup.r 2
      simpa only [DihedralGroup.r.injEq] using cast_mod_two_eq_zero_iff i
  | sr i =>
      change DihedralGroup.sr ((ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) i) =
          DihedralGroup.r 0 ↔ DihedralGroup.sr i = DihedralGroup.r 0 ∨
            DihedralGroup.sr i = DihedralGroup.r 2
      simp only [reduceCtorEq, false_or]

instance centralSignSubgroup_normal : centralSignSubgroup.Normal := by
  rw [← projectivize_kernel_eq_centralSign]
  infer_instance

/-- The range of a surjective group homomorphism is canonically equivalent to
the target group. -/
def rangeEquivTarget : projectivize.range ≃* SheetProjectiveV4 where
  toFun x := x.1
  invFun y := ⟨y, projectivize_surjective y⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Actual central-sign quotient, obtained through Mathlib's first
isomorphism theorem. -/
noncomputable def quotientEquivV4 :
    SheetPinExtension ⧸ projectivize.ker ≃* SheetProjectiveV4 :=
  (QuotientGroup.quotientKerEquivRange projectivize).trans rangeEquivTarget

/-- Strong form: quotienting literally by `{1,z}=⟨z⟩` gives Mathlib's
Klein-four model. -/
noncomputable def quotientCentralSignEquivV4 :
    SheetPinExtension ⧸ centralSignSubgroup ≃* SheetProjectiveV4 :=
  (QuotientGroup.congr centralSignSubgroup projectivize.ker
    (MulEquiv.refl SheetPinExtension) (by
      simpa using projectivize_kernel_eq_centralSign.symm)).trans quotientEquivV4

/-- Capstone: the eight-element dihedral Pin extension has a central sign in
the kernel and its projective quotient is genuinely Klein four. -/
theorem projective_sheet_v4_synthesis :
    pinJ * pinJ = 1 ∧ pinGamma * pinGamma = 1 ∧
    centralSign * centralSign = 1 ∧
    (∀ g : SheetPinExtension, centralSign * g = g * centralSign) ∧
    pinJ * pinGamma = centralSign * (pinGamma * pinJ) ∧
    centralSign ∈ projectivize.ker ∧
    projectivize.ker = centralSignSubgroup ∧
    Nonempty (SheetPinExtension ⧸ projectivize.ker ≃* SheetProjectiveV4) := by
  exact ⟨pinJ_sq, pinGamma_sq, centralSign_sq, centralSign_commutes,
    pin_anticommutation, centralSign_in_kernel, projectivize_kernel_eq_centralSign,
    ⟨quotientEquivV4⟩⟩

end ProjectiveSheetV4
