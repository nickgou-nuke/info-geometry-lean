import InfoGeometry.Canonical.SplitOctonionSignalMultiplication
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Gogberashvili signals in the native vector-matrix carrier

The signal multiplication source is pulled back through the older coordinate
`ZornMatrix` carrier.  This file proves the exact coordinate soldering to the
linear `ZornVectorMatrix` carrier used by the derivation API.
-/

namespace InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge

noncomputable section

def oldToVector (X : ZornMatrix ℝ) : ZornVectorMatrix ℝ where
  a := X.a
  v := X.v
  w := X.w
  b := X.b

def vectorToOld (X : ZornVectorMatrix ℝ) : ZornMatrix ℝ where
  a := X.a
  v := X.v
  w := X.w
  b := X.b

noncomputable def oldToVectorEquiv : ZornMatrix ℝ ≃ ZornVectorMatrix ℝ where
  toFun := oldToVector
  invFun := vectorToOld
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

theorem oldToVector_zero :
    oldToVector (0 : ZornMatrix ℝ) = ZornVectorMatrix.zero := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem oldToVector_add (X Y : ZornMatrix ℝ) :
    oldToVector (X + Y) =
      ZornVectorMatrix.add (oldToVector X) (oldToVector Y) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem oldToVector_sub (X Y : ZornMatrix ℝ) :
    oldToVector (X - Y) =
      ZornVectorMatrix.sub (oldToVector X) (oldToVector Y) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem oldToVector_smul (r : ℝ) (X : ZornMatrix ℝ) :
    oldToVector (r • X) =
      ZornVectorMatrix.smul r (oldToVector X) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem oldToVector_mul (X Y : ZornMatrix ℝ) :
    oldToVector (X * Y) =
      ZornVectorMatrix.mul (oldToVector X) (oldToVector Y) := by
  apply ZornVectorMatrix.ext
  · simp [oldToVector, ZornMatrix.mul, ZornVectorMatrix.mul,
      Vec3.dot, ZornVec3.dot, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [oldToVector, ZornMatrix.mul, ZornVectorMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross,
        ZornVec3.cross]
  · funext i
    fin_cases i <;>
      simp [oldToVector, ZornMatrix.mul, ZornVectorMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross,
        ZornVec3.cross]
  · simp [oldToVector, ZornMatrix.mul, ZornVectorMatrix.mul,
      Vec3.dot, ZornVec3.dot, Fin.sum_univ_three]

theorem toNativeVectorZorn_eq_oldToVector (c : ℝ) (s : SignalCoordinates) :
    toNativeVectorZorn c s = oldToVector (toNativeZorn c s) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> simp [toNativeVectorZorn, oldToVector, toNativeZorn, Vec3.sub]
  · funext i
    fin_cases i <;> simp [toNativeVectorZorn, oldToVector, toNativeZorn, Vec3.add]
  · rfl

theorem nativeVectorZorn_signalMul (c : ℝ) (hc : c ≠ 0)
    (s t : SignalCoordinates) :
    toNativeVectorZorn c (signalMul c hc s t) =
      ZornVectorMatrix.mul (toNativeVectorZorn c s) (toNativeVectorZorn c t) := by
  rw [toNativeVectorZorn_eq_oldToVector, toNativeZorn_signalMul,
    oldToVector_mul, toNativeVectorZorn_eq_oldToVector,
    toNativeVectorZorn_eq_oldToVector]

end
end InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge
