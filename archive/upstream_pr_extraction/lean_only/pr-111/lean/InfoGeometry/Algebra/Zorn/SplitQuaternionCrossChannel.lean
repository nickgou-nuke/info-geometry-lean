/-
Quaternionic cross channel inside the split-octonion carrier.

The cross term in the quaternionic-pair presentation of a split octonion is
the antisymmetric quaternion product, not an independently postulated
three-dimensional vector product.
-/

import InfoGeometry.Algebra.Zorn.SplitQuaternionCore

noncomputable section

namespace InfoGeometry.Algebra.Zorn.SplitQuaternionCrossChannel

open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-- The quaternionic cross channel, written as the antisymmetric product. -/
def quaternionicCross (X Y : CanonicalZorn) : CanonicalZorn :=
  (1 / 2 : ℝ) • (zMul X Y - zMul Y X)

/-- A chiral-parity twist of the same quaternionic channel. -/
def chiralQuaternionicCross (χ : ℝ) (X Y : CanonicalZorn) : CanonicalZorn :=
  χ • quaternionicCross X Y

@[simp] theorem quaternionicCross_anticomm (X Y : CZ) :
    quaternionicCross Y X = -quaternionicCross X Y := by
  unfold quaternionicCross
  module

@[simp] theorem chiralQuaternionicCross_one (X Y : CZ) :
    chiralQuaternionicCross 1 X Y = quaternionicCross X Y := by
  simp only [chiralQuaternionicCross, one_smul]

/-- On the split-quaternion core, the cross channel is the expected generator.
In particular, `i × l = k` because `i l = - l i`. -/
theorem quaternionicCross_i_l :
    quaternionicCross iUnit lUnit = kUnit := by
  unfold quaternionicCross
  rw [k_eq_il, il_eq_neg_li]
  module

end InfoGeometry.Algebra.Zorn.SplitQuaternionCrossChannel
