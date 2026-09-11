import InfoGeometry.Physics.Octonion.ChiralZornAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AkivisIdentity

/-!
# The additive/multiplicative carrier for operator-valued Zorn matrices

This file supplies only the distributive and zero laws needed by the generic
Akivis layer.  It deliberately does not assert alternativity or a Malcev
structure for noncommutative coefficient rings.
-/

namespace InfoGeometry.Canonical.ChiralZorn

open InfoGeometry.Physics.Octonion
open ChiralZornMatrix

variable {A : Type*} [Ring A]

private theorem ext {X Y : ChiralZornMatrix A}
    (hnp : X.n_plus = Y.n_plus) (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) : X = Y := by
  cases X
  cases Y
  simp_all

private theorem colorDot_add_left (x y z : Fin 3 → A) :
    colorDot (x + y) z = colorDot x z + colorDot y z := by
  simp [colorDot, add_mul]
  abel

private theorem colorDot_add_right (x y z : Fin 3 → A) :
    colorDot x (y + z) = colorDot x y + colorDot x z := by
  simp [colorDot, mul_add]
  abel

private theorem colorCross_add_left (x y z : Fin 3 → A) (c : Fin 3) :
    colorCross (x + y) z c = colorCross x z c + colorCross y z c := by
  simp [colorCross, add_mul]
  abel

private theorem colorCross_add_right (x y z : Fin 3 → A) (c : Fin 3) :
    colorCross x (y + z) c = colorCross x y c + colorCross x z c := by
  simp [colorCross, mul_add]
  abel

private theorem left_distrib (X Y Z : ChiralZornMatrix A) :
    X * (Y + Z) = X * Y + X * Z := by
  apply ext
  · change
      X.n_plus * (Y.n_plus + Z.n_plus) + colorDot X.sigma_plus (Y.sigma_minus + Z.sigma_minus) =
        (X.n_plus * Y.n_plus + colorDot X.sigma_plus Y.sigma_minus) +
          (X.n_plus * Z.n_plus + colorDot X.sigma_plus Z.sigma_minus)
    rw [colorDot_add_right]
    simp [mul_add]
    abel
  · change
      colorDot X.sigma_minus (Y.sigma_plus + Z.sigma_plus) + X.n_minus * (Y.n_minus + Z.n_minus) =
        (colorDot X.sigma_minus Y.sigma_plus + X.n_minus * Y.n_minus) +
          (colorDot X.sigma_minus Z.sigma_plus + X.n_minus * Z.n_minus)
    rw [colorDot_add_right]
    simp [mul_add]
    abel
  · funext c
    change
      X.n_plus * (Y.sigma_plus c + Z.sigma_plus c) +
          X.sigma_plus c * (Y.n_minus + Z.n_minus) -
          colorCross X.sigma_minus (Y.sigma_minus + Z.sigma_minus) c =
        (X.n_plus * Y.sigma_plus c + X.sigma_plus c * Y.n_minus -
            colorCross X.sigma_minus Y.sigma_minus c) +
          (X.n_plus * Z.sigma_plus c + X.sigma_plus c * Z.n_minus -
            colorCross X.sigma_minus Z.sigma_minus c)
    rw [colorCross_add_right]
    simp [mul_add]
    abel
  · funext c
    change
      X.sigma_minus c * (Y.n_plus + Z.n_plus) +
          X.n_minus * (Y.sigma_minus c + Z.sigma_minus c) +
          colorCross X.sigma_plus (Y.sigma_plus + Z.sigma_plus) c =
        (X.sigma_minus c * Y.n_plus + X.n_minus * Y.sigma_minus c +
            colorCross X.sigma_plus Y.sigma_plus c) +
          (X.sigma_minus c * Z.n_plus + X.n_minus * Z.sigma_minus c +
            colorCross X.sigma_plus Z.sigma_plus c)
    rw [colorCross_add_right]
    simp [add_mul, mul_add]
    abel

private theorem right_distrib (X Y Z : ChiralZornMatrix A) :
    (X + Y) * Z = X * Z + Y * Z := by
  apply ext
  · change
      (X.n_plus + Y.n_plus) * Z.n_plus + colorDot (X.sigma_plus + Y.sigma_plus) Z.sigma_minus =
        (X.n_plus * Z.n_plus + colorDot X.sigma_plus Z.sigma_minus) +
          (Y.n_plus * Z.n_plus + colorDot Y.sigma_plus Z.sigma_minus)
    rw [colorDot_add_left]
    simp [add_mul]
    abel
  · change
      colorDot (X.sigma_minus + Y.sigma_minus) Z.sigma_plus +
          (X.n_minus + Y.n_minus) * Z.n_minus =
        (colorDot X.sigma_minus Z.sigma_plus + X.n_minus * Z.n_minus) +
          (colorDot Y.sigma_minus Z.sigma_plus + Y.n_minus * Z.n_minus)
    rw [colorDot_add_left]
    simp [add_mul]
    abel
  · funext c
    change
      (X.n_plus + Y.n_plus) * Z.sigma_plus c +
          (X.sigma_plus c + Y.sigma_plus c) * Z.n_minus -
          colorCross (X.sigma_minus + Y.sigma_minus) Z.sigma_minus c =
        (X.n_plus * Z.sigma_plus c + X.sigma_plus c * Z.n_minus -
            colorCross X.sigma_minus Z.sigma_minus c) +
          (Y.n_plus * Z.sigma_plus c + Y.sigma_plus c * Z.n_minus -
            colorCross Y.sigma_minus Z.sigma_minus c)
    rw [colorCross_add_left]
    simp [add_mul]
    abel
  · funext c
    change
      (X.sigma_minus c + Y.sigma_minus c) * Z.n_plus +
          (X.n_minus + Y.n_minus) * Z.sigma_minus c +
          colorCross (X.sigma_plus + Y.sigma_plus) Z.sigma_plus c =
        (X.sigma_minus c * Z.n_plus + X.n_minus * Z.sigma_minus c +
            colorCross X.sigma_plus Z.sigma_plus c) +
          (Y.sigma_minus c * Z.n_plus + Y.n_minus * Z.sigma_minus c +
            colorCross Y.sigma_plus Z.sigma_plus c)
    rw [colorCross_add_left]
    simp [add_mul]
    abel

private theorem mul_zero (X : ChiralZornMatrix A) : X * 0 = 0 := by
  apply ext
  · change X.n_plus * 0 + colorDot X.sigma_plus (fun _ => 0) = 0
    simp [colorDot]
  · change colorDot X.sigma_minus (fun _ => 0) + X.n_minus * 0 = 0
    simp [colorDot]
  · funext c
    change X.n_plus * 0 + X.sigma_plus c * 0 - colorCross X.sigma_minus (fun _ => 0) c = 0
    simp [colorCross]
  · funext c
    change X.sigma_minus c * 0 + X.n_minus * 0 + colorCross X.sigma_plus (fun _ => 0) c = 0
    simp [colorCross]

private theorem zero_mul (X : ChiralZornMatrix A) : 0 * X = 0 := by
  apply ext
  · change 0 * X.n_plus + colorDot (fun _ => 0) X.sigma_minus = 0
    simp [colorDot]
  · change colorDot (fun _ => 0) X.sigma_plus + 0 * X.n_minus = 0
    simp [colorDot]
  · funext c
    change 0 * X.sigma_plus c + 0 * X.n_minus - colorCross (fun _ => 0) X.sigma_minus c = 0
    simp [colorCross]
  · funext c
    change (fun _ => 0) c * X.n_plus + 0 * X.sigma_minus c + colorCross (fun _ => 0) X.sigma_plus c = 0
    simp [colorCross]

/-- The exact additive/multiplicative contract needed by generic Akivis theory. -/
def chiralZornNonUnitalNonAssocRing : NonUnitalNonAssocRing (ChiralZornMatrix A) :=
  { left_distrib := left_distrib
    right_distrib := right_distrib
    zero_mul := zero_mul
    mul_zero := mul_zero }

theorem akivis_identity_on_chiral_zorn (x y z : ChiralZornMatrix A) :
    letI := chiralZornNonUnitalNonAssocRing (A := A)
    InfoGeometry.Algebra.akivisJacobiator x y z =
      _root_.associator x y z + _root_.associator y z x +
        _root_.associator z x y - _root_.associator y x z -
          _root_.associator z y x - _root_.associator x z y := by
  letI := chiralZornNonUnitalNonAssocRing (A := A)
  exact InfoGeometry.Algebra.akivis_identity x y z

theorem regular_representation_defect_on_chiral_zorn
    (x y z : ChiralZornMatrix A) :
    letI := chiralZornNonUnitalNonAssocRing (A := A)
    InfoGeometry.Algebra.leftMultiplicationCommutatorDefect x y z =
      -_root_.associator x y z + _root_.associator y x z := by
  letI := chiralZornNonUnitalNonAssocRing (A := A)
  exact InfoGeometry.Algebra.leftMultiplicationCommutatorDefect_eq_associator_difference
    x y z

def chiralZornRightNestedBianchi
    (x y z : ChiralZornMatrix A) : ChiralZornMatrix A :=
  letI := chiralZornNonUnitalNonAssocRing (A := A)
  InfoGeometry.Algebra.rightNestedJacobiator x y z

theorem chiralZornRightNestedBianchi_eq_neg_jacobiator
    (x y z : ChiralZornMatrix A) :
    letI := chiralZornNonUnitalNonAssocRing (A := A)
    chiralZornRightNestedBianchi x y z =
      -InfoGeometry.Algebra.akivisJacobiator x y z := by
  letI := chiralZornNonUnitalNonAssocRing (A := A)
  simpa [chiralZornRightNestedBianchi] using
    (InfoGeometry.Algebra.rightNestedJacobiator_eq_neg x y z)

theorem chiralZornRightNestedBianchi_eq_neg_associator_sum
    (x y z : ChiralZornMatrix A) :
    letI := chiralZornNonUnitalNonAssocRing (A := A)
    chiralZornRightNestedBianchi x y z =
      -(_root_.associator x y z + _root_.associator y z x +
        _root_.associator z x y - _root_.associator y x z -
          _root_.associator z y x - _root_.associator x z y) := by
  letI := chiralZornNonUnitalNonAssocRing (A := A)
  rw [chiralZornRightNestedBianchi_eq_neg_jacobiator]
  rw [InfoGeometry.Algebra.akivis_identity]

end InfoGeometry.Canonical.ChiralZorn
