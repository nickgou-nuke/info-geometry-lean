/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
UNCOMPILED REVIEW CANDIDATE — not kernel certification.

The only new interface is the compatibility of the Stream 2 local record with
its existing native Zorn carrier. No new multiplication table, group, flow,
associative instance, or exceptional-group identification is introduced.

Convention frozen: local (re, im, u, v) maps to native (a=re, v=u, w=v, b=im).
Native explicit multiplication remains nonassociative.
-/

namespace AcceptanceReview20261024.Flow

open InfoGeometry.Algebra
open InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22

variable {R : Type*} [CommRing R]

/-- Repack all eight local coordinates, without any sign change. -/
def toNative (x : SplitOctonion R) : ZornVectorMatrix R :=
  ⟨x.re, ![x.u0, x.u1, x.u2], ![x.v0, x.v1, x.v2], x.im⟩

/-- The inverse repacking uses the native field order, not the signed Catto basis. -/
def fromNative (x : ZornVectorMatrix R) : SplitOctonion R :=
  ⟨x.a, x.b, x.v 0, x.v 1, x.v 2, x.w 0, x.w 1, x.w 2⟩

/-- Coordinate equivalence only; multiplication compatibility is stated separately. -/
def localNativeEquiv : SplitOctonion R ≃ ZornVectorMatrix R where
  toFun := toNative
  invFun := fromNative
  left_inv x := by cases x; rfl
  right_inv x := by
    apply ZornVectorMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl

theorem toNative_one :
    toNative (SplitOctonion.one : SplitOctonion R) = ZornVectorMatrix.one := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toNative_add (x y : SplitOctonion R) :
    toNative (SplitOctonion.add x y) = ZornVectorMatrix.add (toNative x) (toNative y) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toNative_neg (x : SplitOctonion R) :
    toNative (SplitOctonion.neg x) = ZornVectorMatrix.neg (toNative x) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

/-- Compatibility with the full native nonassociative product over any commutative ring. -/
theorem toNative_mul (x y : SplitOctonion R) :
    toNative (SplitOctonion.mul x y) = ZornVectorMatrix.mul (toNative x) (toNative y) := by
  apply ZornVectorMatrix.ext
  · simp [toNative, SplitOctonion.mul, ZornVectorMatrix.mul,
      ZornVec3.dot, Fin.sum_univ_three]
    <;> ring
  · funext i
    fin_cases i <;>
      simp [toNative, SplitOctonion.mul, ZornVectorMatrix.mul, ZornVec3.cross] <;> ring
  · funext i
    fin_cases i <;>
      simp [toNative, SplitOctonion.mul, ZornVectorMatrix.mul, ZornVec3.cross] <;> ring
  · simp [toNative, SplitOctonion.mul, ZornVectorMatrix.mul,
      ZornVec3.dot, Fin.sum_univ_three]
    <;> ring

end AcceptanceReview20261024.Flow
