import proofs.SplitOctonionQuaternionChart
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

open Quaternion
open SplitOctonion

namespace SplitOctonion

instance : AddCommGroup SplitOct where
  add_assoc := by intros a b c; ext1 <;> ext1 <;> simp [add_def] <;> ring
  zero_add := by intros a; ext1 <;> ext1 <;> simp [add_def, zero_def] <;> ring
  add_zero := by intros a; ext1 <;> ext1 <;> simp [add_def, zero_def] <;> ring
  add_comm := by intros a b; ext1 <;> ext1 <;> simp [add_def] <;> ring
  neg_add_cancel := by intros a; ext1 <;> ext1 <;> simp [add_def, neg_def, zero_def] <;> ring
  sub_eq_add_neg := by intros a b; ext1 <;> ext1 <;> simp [add_def, sub_def, neg_def] <;> ring
  nsmul := nsmulRec
  nsmul_zero := by intro a; rfl
  nsmul_succ := by intro n a; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro a; rfl
  zsmul_succ' := by intro n a; rfl
  zsmul_neg' := by intro n a; rfl

instance : NonUnitalNonAssocRing SplitOct where
  left_distrib := by intros a b c; ext1 <;> ext1 <;> simp [add_def, mul_def, star] <;> ring
  right_distrib := by intros a b c; ext1 <;> ext1 <;> simp [add_def, mul_def, star] <;> ring
  zero_mul := by intros a; ext1 <;> ext1 <;> simp [add_def, mul_def, zero_def, star] <;> ring
  mul_zero := by intros a; ext1 <;> ext1 <;> simp [add_def, mul_def, zero_def, star] <;> ring

instance : NonAssocRing SplitOct where
  one_mul := by intros a; ext1 <;> ext1 <;> simp [mul_def, one_def, star] <;> ring
  mul_one := by intros a; ext1 <;> ext1 <;> simp [mul_def, one_def, star] <;> ring
  
instance : Module ℝ SplitOct where
  smul_zero := by intros a; ext1 <;> ext1 <;> simp [smul_def, zero_def] <;> ring
  zero_smul := by intros a; ext1 <;> ext1 <;> simp [smul_def, zero_def] <;> ring
  add_smul := by intros a b c; ext1 <;> ext1 <;> simp [smul_def, add_def] <;> ring
  smul_add := by intros a b c; ext1 <;> ext1 <;> simp [smul_def, add_def] <;> ring
  mul_smul := by intros a b c; ext1 <;> ext1 <;> simp [smul_def, mul_def] <;> ring
  one_smul := by intros a; ext1 <;> ext1 <;> simp [smul_def] <;> ring

instance : SMulCommClass ℝ SplitOct SplitOct where
  smul_comm := by intros a b c; ext1 <;> ext1 <;> simp [smul_def, mul_def, star] <;> ring

instance : IsScalarTower ℝ SplitOct SplitOct where
  smul_assoc := by intros a b c; ext1 <;> ext1 <;> simp [smul_def, mul_def, star] <;> ring

end SplitOctonion
