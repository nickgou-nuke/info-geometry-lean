/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.OperatorAlgebra.SplitOctonions.FureyLadderCAR
import InfoGeometry.Algebra.ZornMatrix

/-!
# Scalar/coordinate bridge for the Furey Zorn carrier

The Furey owner uses the canonical `x/y` Zorn coordinates over `ℚ`, while the
current real chiral owner uses the `v/w` presentation over `ℝ`.  This file
records the explicit coordinate map.  It deliberately does not identify the
two structures definitionally.
-/

namespace InfoGeometry.Algebra.SplitOctonionFureyScalarBridge

abbrev QZ := InfoGeometry.Canonical.ZornMatrix ℚ
abbrev RZ := InfoGeometry.Algebra.ZornMatrix ℝ

def ratToRealZorn : QZ → RZ := fun Z =>
  { a := Z.a,
    v := fun i => Z.x i,
    w := fun i => Z.y i,
    b := Z.b }

@[simp] theorem ratToRealZorn_a (Z : QZ) :
    (ratToRealZorn Z).a = Z.a := rfl

@[simp] theorem ratToRealZorn_b (Z : QZ) :
    (ratToRealZorn Z).b = Z.b := rfl

@[simp] theorem ratToRealZorn_v (Z : QZ) (i : Fin 3) :
    (ratToRealZorn Z).v i = Z.x i := rfl

@[simp] theorem ratToRealZorn_w (Z : QZ) (i : Fin 3) :
    (ratToRealZorn Z).w i = Z.y i := rfl

theorem ratToRealZorn_injective : Function.Injective ratToRealZorn := by
  intro X Y h
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · have ha : (X.a : ℝ) = (Y.a : ℝ) := by
      simpa [ratToRealZorn] using congrArg (fun Z : RZ => Z.a) h
    exact_mod_cast ha
  · have hb : (X.b : ℝ) = (Y.b : ℝ) := by
      simpa [ratToRealZorn] using congrArg (fun Z : RZ => Z.b) h
    exact_mod_cast hb
  · have hx := congrArg (fun Z : RZ => Z.v) h
    funext i
    have hxi : (X.x i : ℝ) = (Y.x i : ℝ) := by
      simpa [ratToRealZorn] using congrFun hx i
    exact_mod_cast hxi
  · have hy := congrArg (fun Z : RZ => Z.w) h
    funext i
    have hyi : (X.y i : ℝ) = (Y.y i : ℝ) := by
      simpa [ratToRealZorn] using congrFun hy i
    exact_mod_cast hyi

theorem ratToRealZorn_add (X Y : QZ) :
    ratToRealZorn (X + Y) = ratToRealZorn X + ratToRealZorn Y := by
  apply InfoGeometry.Algebra.ZornMatrix.ext <;>
    simp [ratToRealZorn, InfoGeometry.Algebra.ZornMatrix.add]
  all_goals funext i; fin_cases i <;> rfl

theorem ratToRealZorn_smul (c : ℚ) (X : QZ) :
    ratToRealZorn (c • X) = (c : ℝ) • ratToRealZorn X := by
  apply InfoGeometry.Algebra.ZornMatrix.ext <;>
    simp [ratToRealZorn, InfoGeometry.Algebra.ZornMatrix.smul]
  all_goals funext i; fin_cases i <;> rfl

theorem ratToRealZorn_mul (X Y : QZ) :
    ratToRealZorn (X * Y) = ratToRealZorn X * ratToRealZorn Y := by
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · change ((X.a * Y.a + InfoGeometry.Canonical.ZornMatrix.dot X.x Y.y : ℚ) : ℝ) = _
    simp [ratToRealZorn, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot]
  · funext i
    fin_cases i <;>
      simp [ratToRealZorn, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.cross,
        InfoGeometry.Algebra.Vec3.add,
        InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.Vec3.smul, Pi.smul_apply, Matrix.vecHead,
        Matrix.vecTail] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [ratToRealZorn, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.cross,
        InfoGeometry.Algebra.Vec3.add,
        InfoGeometry.Algebra.Vec3.smul, Pi.smul_apply, Matrix.vecHead,
        Matrix.vecTail] <;>
      ring
  · simp [ratToRealZorn, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot] <;> ring

theorem ratToRealZorn_up_one_mul_down_one :
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1) =
      ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.ePlus := by
  calc
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1) =
        ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1) *
          ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1) :=
      ratToRealZorn_mul _ _
    _ = ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.ePlus := by
      exact (ratToRealZorn_mul _ _).symm.trans
        (congrArg ratToRealZorn
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up_one_mul_down_one)

theorem ratToRealZorn_up_two_mul_down_two :
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) =
      ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.ePlus := by
  calc
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) =
        ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) *
          ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) :=
      ratToRealZorn_mul _ _
    _ = ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.ePlus := by
      exact (ratToRealZorn_mul _ _).symm.trans
        (congrArg ratToRealZorn
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up_two_mul_down_two)

theorem ratToRealZorn_up_one_mul_down_two :
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) =
      ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.zeroZ := by
  calc
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) =
        ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1) *
          ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) :=
      ratToRealZorn_mul _ _
    _ = ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.zeroZ := by
      exact (ratToRealZorn_mul _ _).symm.trans
        (congrArg ratToRealZorn
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up_one_mul_down_two)

theorem ratToRealZorn_down_one_mul_up_two :
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) =
      ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.zeroZ := by
  calc
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) =
        ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1) *
          ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) :=
      ratToRealZorn_mul _ _
    _ = ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.zeroZ := by
      exact (ratToRealZorn_mul _ _).symm.trans
        (congrArg ratToRealZorn
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down_one_mul_up_two)

theorem ratToRealZorn_down_two_mul_up_two :
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) =
      ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.eMinus := by
  calc
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) =
        ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 2) *
          ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 2) :=
      ratToRealZorn_mul _ _
    _ = ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.eMinus := by
      exact (ratToRealZorn_mul _ _).symm.trans
        (congrArg ratToRealZorn
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down_two_mul_up_two)

theorem ratToRealZorn_down_one_mul_up_one :
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1) =
      ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.eMinus := by
  calc
    ratToRealZorn
        (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1 *
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1) =
        ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down 1) *
          ratToRealZorn (InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.up 1) :=
      ratToRealZorn_mul _ _
    _ = ratToRealZorn InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.eMinus := by
      exact (ratToRealZorn_mul _ _).symm.trans
        (congrArg ratToRealZorn
          InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR.down_one_mul_up_one)

end InfoGeometry.Algebra.SplitOctonionFureyScalarBridge
