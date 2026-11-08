import InfoGeometry.Algebra.RealSplitAlbert
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornCore

/-!
# Coordinate bridge: real split octonions and the native Zorn carrier

`RealSplitOct` and `ZornCore.Zorn` are two coordinate presentations of the
same split-octonion multiplication law.  This file identifies those carriers
without introducing an associative replacement for their nonassociative
product.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealSplitOctZornCoreBridge

open InfoGeometry.Algebra

def realSplitOctToZornCore (X : RealSplitOct) : ZornCore.Zorn where
  a := X.a
  u := ![X.x0, X.x1, X.x2]
  v := ![X.y0, X.y1, X.y2]
  b := X.b

def zornCoreToRealSplitOct (X : ZornCore.Zorn) : RealSplitOct where
  a := X.a
  b := X.b
  x0 := X.u 0
  x1 := X.u 1
  x2 := X.u 2
  y0 := X.v 0
  y1 := X.v 1
  y2 := X.v 2

@[simp] theorem zornCoreToRealSplitOct_realSplitOctToZornCore
    (X : RealSplitOct) :
    zornCoreToRealSplitOct (realSplitOctToZornCore X) = X := by
  cases X
  ext <;> rfl

@[simp] theorem realSplitOctToZornCore_zornCoreToRealSplitOct
    (X : ZornCore.Zorn) :
    realSplitOctToZornCore (zornCoreToRealSplitOct X) = X := by
  apply ZornCore.Zorn.ext'
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

noncomputable def realSplitOctZornEquiv : RealSplitOct ≃ ZornCore.Zorn where
  toFun := realSplitOctToZornCore
  invFun := zornCoreToRealSplitOct
  left_inv := zornCoreToRealSplitOct_realSplitOctToZornCore
  right_inv := realSplitOctToZornCore_zornCoreToRealSplitOct

theorem realSplitOctToZornCore_mul (X Y : RealSplitOct) :
    realSplitOctToZornCore (RealSplitOct.mul X Y) =
      realSplitOctToZornCore X * realSplitOctToZornCore Y := by
  apply ZornCore.Zorn.ext'
  · simp [realSplitOctToZornCore, RealSplitOct.mul, ZornCore.dot,
      Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [realSplitOctToZornCore, RealSplitOct.mul, ZornCore.cross]
  · funext i
    fin_cases i <;>
      simp [realSplitOctToZornCore, RealSplitOct.mul, ZornCore.cross]
  · simp [realSplitOctToZornCore, RealSplitOct.mul, ZornCore.dot,
      Fin.sum_univ_three] <;>
      ring

end InfoGeometry.Canonical.RealSplitOctZornCoreBridge
