import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.Concrete

/-!
# Orientation-twisted coordinate symmetry of the Zorn product

The ordinary permutation action on the three vector coordinates preserves the
dot product, but an odd permutation reverses the Levi-Civita/cross-product
channel.  Twisting both Zorn vector rails by the sign character repairs this
orientation defect and gives an actual automorphism of `ZornCell.mulZ`.

This is the coordinate `S₃` statement only.  It is not a triality theorem,
and it does not identify the coordinate action with a Spin(8) sector action.
-/

namespace InfoGeometry.Canonical.ZornOrientationTwistedS3

set_option maxHeartbeats 1000000

open InfoGeometry.Algebra.Zorn.Concrete

abbrev Vec3 := InfoGeometry.Algebra.FiniteSpin.Vec3C

def permutationSign (p : Equiv.Perm (Fin 3)) : ℂ :=
  (Equiv.Perm.sign p : ℤ)

def permuteVec (p : Equiv.Perm (Fin 3)) (x : Vec3) : Vec3 :=
  fun i => x (p⁻¹ i)

def twistedVec (p : Equiv.Perm (Fin 3)) (x : Vec3) : Vec3 :=
  permutationSign p • permuteVec p x

theorem twistedVec_comp (p q : Equiv.Perm (Fin 3)) (x : Vec3) :
    twistedVec (p * q) x = twistedVec p (twistedVec q x) := by
  classical
  fin_cases p <;> fin_cases q <;> funext i <;> fin_cases i <;>
    simp [twistedVec, permutationSign, permuteVec,
      Equiv.Perm.sign_mul, Equiv.swap_apply_def]

@[simp] theorem twistedVec_one (x : Vec3) :
    twistedVec 1 x = x := by
  funext i
  simp [twistedVec, permutationSign, permuteVec]

def xVec (X : ZornCell ℂ) : Vec3 :=
  ![X.x1, X.x2, X.x3]

def yVec (X : ZornCell ℂ) : Vec3 :=
  ![X.y1, X.y2, X.y3]

/-- The sign-twisted coordinate action on both Zorn vector rails. -/
def zornAction (p : Equiv.Perm (Fin 3)) (X : ZornCell ℂ) : ZornCell ℂ where
  r := X.r
  s := X.s
  x1 := twistedVec p (xVec X) 0
  x2 := twistedVec p (xVec X) 1
  x3 := twistedVec p (xVec X) 2
  y1 := twistedVec p (yVec X) 0
  y2 := twistedVec p (yVec X) 1
  y3 := twistedVec p (yVec X) 2

theorem zornCell_ext {X Y : ZornCell ℂ}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) :
    X = Y := by
  cases X
  cases Y
  simp_all

@[simp] theorem zornAction_r (p : Equiv.Perm (Fin 3)) (X : ZornCell ℂ) :
    (zornAction p X).r = X.r := rfl

@[simp] theorem zornAction_s (p : Equiv.Perm (Fin 3)) (X : ZornCell ℂ) :
    (zornAction p X).s = X.s := rfl

theorem zornAction_mulZ (p : Equiv.Perm (Fin 3)) (X Y : ZornCell ℂ) :
    zornAction p (ZornCell.mulZ X Y) =
      ZornCell.mulZ (zornAction p X) (zornAction p Y) := by
  classical
  fin_cases p <;>
    apply zornCell_ext <;>
    simp [zornAction, twistedVec, permuteVec, permutationSign,
      xVec, yVec, ZornCell.mulZ, Equiv.swap_apply_def] <;>
    ring

theorem zornAction_mul (p : Equiv.Perm (Fin 3)) (X Y : ZornCell ℂ) :
    zornAction p (X * Y) = zornAction p X * zornAction p Y := by
  exact zornAction_mulZ p X Y

theorem zornAction_one (X : ZornCell ℂ) : zornAction 1 X = X := by
  apply zornCell_ext <;>
    simp [zornAction, twistedVec, permuteVec, permutationSign, xVec, yVec]

theorem zornAction_comp (p q : Equiv.Perm (Fin 3)) (X : ZornCell ℂ) :
    zornAction (p * q) X = zornAction p (zornAction q X) := by
  have hx : xVec (zornAction q X) = twistedVec q (xVec X) := by
    funext i
    fin_cases i <;> rfl
  have hy : yVec (zornAction q X) = twistedVec q (yVec X) := by
    funext i
    fin_cases i <;> rfl
  apply zornCell_ext
  · rfl
  · rfl
  · change twistedVec (p * q) (xVec X) 0 =
      twistedVec p (xVec (zornAction q X)) 0
    rw [hx, twistedVec_comp]
  · change twistedVec (p * q) (xVec X) 1 =
      twistedVec p (xVec (zornAction q X)) 1
    rw [hx, twistedVec_comp]
  · change twistedVec (p * q) (xVec X) 2 =
      twistedVec p (xVec (zornAction q X)) 2
    rw [hx, twistedVec_comp]
  · change twistedVec (p * q) (yVec X) 0 =
      twistedVec p (yVec (zornAction q X)) 0
    rw [hy, twistedVec_comp]
  · change twistedVec (p * q) (yVec X) 1 =
      twistedVec p (yVec (zornAction q X)) 1
    rw [hy, twistedVec_comp]
  · change twistedVec (p * q) (yVec X) 2 =
      twistedVec p (yVec (zornAction q X)) 2
    rw [hy, twistedVec_comp]

end InfoGeometry.Canonical.ZornOrientationTwistedS3
