import InfoGeometry.Canonical.ChiralZornFiniteSymmetry
import InfoGeometry.Canonical.NonAbelianDihedralSymmetry12

/-!
# The structural twist on the chiral Zorn carrier

The raw sheet exchange is not multiplicative because it reverses the oriented
cross channel.  The existing `reflect` operation combines that sheet exchange
with the orientation-reversing colour permutation.  This file gives the
resulting automorphism a small reusable API and records covariance of the
ordinary commutator and associator.  No Lie or super-Lie instance is claimed.
-/

namespace InfoGeometry.Physics.Octonion.ChiralZornMatrix

noncomputable section

variable {A : Type*} [Ring A]

abbrev twistedSheetOrientation : ChiralZornMatrix A ≃* ChiralZornMatrix A :=
  reflectMulEquiv

@[simp] theorem twistedSheetOrientation_apply (X : ChiralZornMatrix A) :
    twistedSheetOrientation X = reflect X := rfl

theorem twistedSheetOrientation_mul (X Y : ChiralZornMatrix A) :
    twistedSheetOrientation (X * Y) =
      twistedSheetOrientation X * twistedSheetOrientation Y := by
  exact reflect_mul X Y

theorem twistedSheetOrientation_involutive (X : ChiralZornMatrix A) :
    twistedSheetOrientation (twistedSheetOrientation X) = X := by
  exact reflect_two X

theorem twistedSheetOrientation_add (X Y : ChiralZornMatrix A) :
    twistedSheetOrientation (X + Y) =
      twistedSheetOrientation X + twistedSheetOrientation Y := by
  rfl

theorem twistedSheetOrientation_neg (X : ChiralZornMatrix A) :
    twistedSheetOrientation (-X) = -twistedSheetOrientation X := by
  rfl

theorem twistedSheetOrientation_sub (X Y : ChiralZornMatrix A) :
    twistedSheetOrientation (X - Y) =
      twistedSheetOrientation X - twistedSheetOrientation Y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, twistedSheetOrientation_add,
    twistedSheetOrientation_neg]

def ordinaryCommutator (X Y : ChiralZornMatrix A) : ChiralZornMatrix A :=
  X * Y - Y * X

theorem twistedSheetOrientation_commutator (X Y : ChiralZornMatrix A) :
    twistedSheetOrientation (ordinaryCommutator X Y) =
      ordinaryCommutator (twistedSheetOrientation X)
        (twistedSheetOrientation Y) := by
  unfold ordinaryCommutator
  rw [twistedSheetOrientation_sub, twistedSheetOrientation_mul,
    twistedSheetOrientation_mul]

def ordinaryAssociator
    (X Y Z : ChiralZornMatrix A) : ChiralZornMatrix A :=
  (X * Y) * Z - X * (Y * Z)

theorem twistedSheetOrientation_associator (X Y Z : ChiralZornMatrix A) :
    twistedSheetOrientation (ordinaryAssociator X Y Z) =
      ordinaryAssociator (twistedSheetOrientation X)
        (twistedSheetOrientation Y) (twistedSheetOrientation Z) := by
  unfold ordinaryAssociator
  rw [twistedSheetOrientation_sub, twistedSheetOrientation_mul,
    twistedSheetOrientation_mul, twistedSheetOrientation_mul,
    twistedSheetOrientation_mul]

theorem twistedSheetOrientation_conjugates_rotation :
    (twistedSheetOrientation : ChiralZornMatrix A ≃* ChiralZornMatrix A) *
        rotateMulEquiv * twistedSheetOrientation = rotateMulEquiv ^ 2 := by
  exact M_R_M_equiv (A := A)

end
end InfoGeometry.Physics.Octonion.ChiralZornMatrix
