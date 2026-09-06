import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic

open Quaternion

namespace SplitOctonion

structure SplitOct where
  a : Quaternion ℝ
  b : Quaternion ℝ

@[ext] lemma SplitOct.ext (x y : SplitOct) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

instance : Mul SplitOct where mul x y := ⟨x.a * y.a + (star y.b) * x.b, y.b * x.a + x.b * (star y.a)⟩
@[simp] lemma mul_def (x y : SplitOct) : x * y = ⟨x.a * y.a + (star y.b) * x.b, y.b * x.a + x.b * (star y.a)⟩ := rfl

instance : Add SplitOct where add x y := ⟨x.a + y.a, x.b + y.b⟩
@[simp] lemma add_def (x y : SplitOct) : x + y = ⟨x.a + y.a, x.b + y.b⟩ := rfl

instance : Sub SplitOct where sub x y := ⟨x.a - y.a, x.b - y.b⟩
@[simp] lemma sub_def (x y : SplitOct) : x - y = ⟨x.a - y.a, x.b - y.b⟩ := rfl

instance : Neg SplitOct where neg x := ⟨-x.a, -x.b⟩
@[simp] lemma neg_def (x : SplitOct) : -x = ⟨-x.a, -x.b⟩ := rfl

instance : SMul ℝ SplitOct where smul c x := ⟨c • x.a, c • x.b⟩
@[simp] lemma smul_def (c : ℝ) (x : SplitOct) : c • x = ⟨c • x.a, c • x.b⟩ := rfl

instance : Zero SplitOct where zero := ⟨0, 0⟩
@[simp] lemma zero_def : (0 : SplitOct) = ⟨0, 0⟩ := rfl

instance : One SplitOct where one := ⟨1, 0⟩
@[simp] lemma one_def : (1 : SplitOct) = ⟨1, 0⟩ := rfl

@[simp] def bracket (x y : SplitOct) : SplitOct := x * y - y * x

def u : SplitOct := ⟨⟨0, 1, 0, 0⟩, 0⟩
def ell : SplitOct := ⟨0, 1⟩

end SplitOctonion
