import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.RingTheory.Derivation.Basic

open Quaternion

structure SplitOct where
  q1 : Quaternion ℝ
  q2 : Quaternion ℝ

namespace SplitOct

noncomputable section
@[ext] lemma ext (x y : SplitOct) (hq1 : x.q1 = y.q1) (hq2 : x.q2 = y.q2) : x = y := by
  cases x; cases y; simp_all

instance : Mul SplitOct where mul x y := ⟨x.q1 * y.q1 + (star y.q2) * x.q2, y.q2 * x.q1 + x.q2 * (star y.q1)⟩
instance : Add SplitOct where add x y := ⟨x.q1 + y.q1, x.q2 + y.q2⟩
instance : Sub SplitOct where sub x y := ⟨x.q1 - y.q1, x.q2 - y.q2⟩
instance : Neg SplitOct where neg x := ⟨-x.q1, -x.q2⟩
instance : Zero SplitOct where zero := ⟨0, 0⟩
instance : One SplitOct where one := ⟨1, 0⟩
instance : SMul ℝ SplitOct where smul c x := ⟨c • x.q1, c • x.q2⟩

@[simp] lemma mul_q1 (x y : SplitOct) : (x * y).q1 = x.q1 * y.q1 + (star y.q2) * x.q2 := rfl
@[simp] lemma mul_q2 (x y : SplitOct) : (x * y).q2 = y.q2 * x.q1 + x.q2 * (star y.q1) := rfl
@[simp] lemma add_q1 (x y : SplitOct) : (x + y).q1 = x.q1 + y.q1 := rfl
@[simp] lemma add_q2 (x y : SplitOct) : (x + y).q2 = x.q2 + y.q2 := rfl
@[simp] lemma sub_q1 (x y : SplitOct) : (x - y).q1 = x.q1 - y.q1 := rfl
@[simp] lemma sub_q2 (x y : SplitOct) : (x - y).q2 = x.q2 - y.q2 := rfl
@[simp] lemma neg_q1 (x : SplitOct) : (-x).q1 = -x.q1 := rfl
@[simp] lemma neg_q2 (x : SplitOct) : (-x).q2 = -x.q2 := rfl
@[simp] lemma zero_q1 : (0 : SplitOct).q1 = 0 := rfl
@[simp] lemma zero_q2 : (0 : SplitOct).q2 = 0 := rfl
@[simp] lemma smul_q1 (c : ℝ) (x : SplitOct) : (c • x).q1 = c • x.q1 := rfl
@[simp] lemma smul_q2 (c : ℝ) (x : SplitOct) : (c • x).q2 = c • x.q2 := rfl

instance : AddCommGroup SplitOct where
  add := (· + ·)
  add_assoc x y z := by ext <;> simp <;> abel
  zero := 0
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul := nsmulRec
  neg := (- ·)
  sub := (· - ·)
  sub_eq_add_neg x y := by ext <;> simp <;> abel
  zsmul := zsmulRec
  neg_add_cancel x := by ext <;> simp <;> abel
  add_comm x y := by ext <;> simp <;> abel

instance : NonUnitalNonAssocRing SplitOct where
  add := (· + ·)
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  neg := (- ·)
  sub := (· - ·)
  sub_eq_add_neg := sub_eq_add_neg
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm
  mul := (· * ·)
  left_distrib x y z := by ext <;> simp [add_mul, mul_add, star_add] <;> abel
  right_distrib x y z := by ext <;> simp [add_mul, mul_add, star_add] <;> abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp

instance : Module ℝ SplitOct where
  smul := (· • ·)
  smul_zero a := by ext <;> simp
  smul_add a x y := by ext <;> simp [smul_add]
  add_smul a b x := by ext <;> simp [add_mul]
  zero_smul x := by ext <;> simp
  one_smul x := by ext <;> simp
  mul_smul a b x := by ext <;> simp [mul_smul]

-- The split unit and spatial unit
def ell : SplitOct := ⟨0, 1⟩
def u : SplitOct := ⟨⟨0, 1, 0, 0⟩, 0⟩

@[simp] def bracket (x y : SplitOct) : SplitOct := x * y - y * x

-- The SL(2, R) Witt Slice
def E : SplitOct := (1/2 : ℝ) • (u + ell * u)
def F : SplitOct := -(1/2 : ℝ) • (u - ell * u)
def H : SplitOct := ell

theorem sl2_HE : bracket H E = (2 : ℝ) • E := by
  ext1 <;> ext1 <;> simp [bracket, E, H, u, ell] <;> ring

theorem sl2_HF : bracket H F = (-2 : ℝ) • F := by
  ext1 <;> ext1 <;> simp [bracket, F, H, u, ell] <;> ring

theorem sl2_EF : bracket E F = H := by
  ext1 <;> ext1 <;> simp [bracket, E, F, H, u, ell, star] <;> ring

-- Derivations and G2 Bridge
def associator (x y z : SplitOct) : SplitOct := (x * y) * z - x * (y * z)

def innerDeriv (x y z : SplitOct) : SplitOct :=
  bracket (bracket x y) z - (3 : ℝ) • associator x y z

def op_H (z : SplitOct) : SplitOct := innerDeriv E F z
def op_E (z : SplitOct) : SplitOct := (1/2 : ℝ) • innerDeriv H E z
def op_F (z : SplitOct) : SplitOct := -(1/2 : ℝ) • innerDeriv H F z

def derivBracket (D1 D2 : SplitOct → SplitOct) (z : SplitOct) : SplitOct :=
  D1 (D2 z) - D2 (D1 z)

theorem g2_root_HE (z : SplitOct) : derivBracket op_H op_E z = (2 : ℝ) • op_E z := by
  sorry

theorem g2_root_HF (z : SplitOct) : derivBracket op_H op_F z = (-2 : ℝ) • op_F z := by
  sorry

theorem g2_root_EF (z : SplitOct) : derivBracket op_E op_F z = op_H z := by
  sorry

end

end SplitOct
