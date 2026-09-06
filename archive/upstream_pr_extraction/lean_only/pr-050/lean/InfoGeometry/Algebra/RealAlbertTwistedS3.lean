import InfoGeometry.Algebra.RealSplitAlbert

namespace InfoGeometry.Algebra

open RealSplitOct

/-! The transposition of the first two diagonal slots in the displayed
Hermitian Albert coordinates is accompanied by split-octonion conjugation on
each transported off-diagonal entry.  This file proves the resulting map for
the concrete product owned by `RealSplitAlbert`; it makes no claim about the
separate `H3Zorn` candidate product. -/

@[simp] theorem RealSplitOct.conj_conj (X : RealSplitOct) :
    RealSplitOct.conj (RealSplitOct.conj X) = X := by
  cases X
  simp [RealSplitOct.conj]

@[simp] theorem RealSplitOct.conj_add (X Y : RealSplitOct) :
    RealSplitOct.conj (X + Y) =
      RealSplitOct.conj X + RealSplitOct.conj Y := by
  change RealSplitOct.conj (RealSplitOct.add X Y) =
    RealSplitOct.add (RealSplitOct.conj X) (RealSplitOct.conj Y)
  cases X <;> cases Y
  simp [RealSplitOct.add, RealSplitOct.conj] <;> ring_nf <;> simp

@[simp] theorem RealSplitOct.conj_smul (r : ℝ) (X : RealSplitOct) :
    RealSplitOct.conj (RealSplitOct.smul r X) =
      RealSplitOct.smul r (RealSplitOct.conj X) := by
  cases X
  simp [RealSplitOct.smul, RealSplitOct.conj]

theorem RealSplitOct.conj_mul (X Y : RealSplitOct) :
    RealSplitOct.conj (RealSplitOct.mul X Y) =
      RealSplitOct.mul (RealSplitOct.conj Y) (RealSplitOct.conj X) := by
  cases X <;> cases Y <;>
    simp [RealSplitOct.mul, RealSplitOct.conj] <;> ring_nf <;> simp

/-- The twisted transposition of the first two Hermitian Albert slots. -/
def twistedS12 (X : RealAlbertMatrix) : RealAlbertMatrix :=
  { α₁ := X.α₂
    α₂ := X.α₁
    α₃ := X.α₃
    z₁ := RealSplitOct.conj X.z₂
    z₂ := RealSplitOct.conj X.z₁
    z₃ := RealSplitOct.conj X.z₃ }

@[simp] theorem twistedS12_involutive (X : RealAlbertMatrix) :
    twistedS12 (twistedS12 X) = X := by
  cases X
  simp [twistedS12]

end InfoGeometry.Algebra
