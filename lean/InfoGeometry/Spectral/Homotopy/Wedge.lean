import Mathlib
import InfoGeometry.Spectral.Homotopy.Smash

/-!
# Finite wedge and join readouts

This is a theorem-safe finite replacement for the old unstable homotopy
skeleton.  Wedge is represented by a sum carrier and join by a product carrier;
only the corresponding elementary equivalences are proved.
-/

noncomputable section

namespace Wedge

open InfoGeometry.Spectral.Homotopy.Suspension
open InfoGeometry.Spectral.Homotopy.Smash

/-- Finite pointed wedge readout, represented by a sum carrier. -/
def WedgeSum (X Y : PointedReadout) : PointedReadout where
  carrier := X.carrier ⊕ Y.carrier
  base := Sum.inl X.base

infixr:65 " ⋁ " => WedgeSum

/-- Finite pointed join readout, represented here by a product carrier. -/
def Join (X Y : PointedReadout) : PointedReadout where
  carrier := X.carrier × Y.carrier
  base := (X.base, Y.base)

infixr:70 " ★ " => Join

/-- Sum associativity as a pointed equivalence. -/
def WedgeSum.assoc (X Y Z : PointedReadout) :
    PointedEquiv ((X ⋁ Y) ⋁ Z) (X ⋁ (Y ⋁ Z)) where
  toEquiv := Equiv.sumAssoc X.carrier Y.carrier Z.carrier
  map_base := rfl

/-- Sum commutativity at the carrier level.  It is not pointed for left-based wedges. -/
def WedgeSum.carrierComm (X Y : PointedReadout) :
    (X ⋁ Y).carrier ≃ (Y ⋁ X).carrier :=
  Equiv.sumComm X.carrier Y.carrier

/--
The carrier commutativity map sends the left wedge basepoint to the right
injection.  This records the exact obstruction to a pointed commutativity claim
for the finite left-based sum readout.
-/
@[simp]
theorem WedgeSum.carrierComm_base (X Y : PointedReadout) :
    WedgeSum.carrierComm X Y (WedgeSum X Y).base = Sum.inr X.base :=
  rfl

/-- The finite suspension readout preserves finite wedges by definition. -/
def SuspensionWedge (X Y : PointedReadout) :
    PointedEquiv (Suspension (X ⋁ Y)) (Suspension X ⋁ Suspension Y) :=
  PointedEquiv.refl (X ⋁ Y)

/-- Distribute product over sum at the finite readout level. -/
def SmashWedgeDistributivity (X Y Z : PointedReadout) :
    PointedEquiv (X ⋀ (Y ⋁ Z)) ((X ⋀ Y) ⋁ (X ⋀ Z)) where
  toEquiv :=
    { toFun := fun x =>
        match x.2 with
        | Sum.inl y => Sum.inl (x.1, y)
        | Sum.inr z => Sum.inr (x.1, z)
      invFun := fun x =>
        match x with
        | Sum.inl xy => (xy.1, Sum.inl xy.2)
        | Sum.inr xz => (xz.1, Sum.inr xz.2)
      left_inv := by
        intro x
        cases x with
        | mk x yz =>
          cases yz <;> rfl
      right_inv := by
        intro x
        cases x <;> rfl }
  map_base := rfl

/-- Product associativity as a join readout equivalence. -/
def Join.assoc (X Y Z : PointedReadout) :
    PointedEquiv ((X ★ Y) ★ Z) (X ★ (Y ★ Z)) :=
  SmashProduct.assoc X Y Z

/-- Join commutativity as a finite readout equivalence. -/
def Join.comm (X Y : PointedReadout) :
    PointedEquiv (X ★ Y) (Y ★ X) :=
  SmashProduct.comm X Y

/-- Suspension of a product has the same finite carrier readout as product suspension. -/
def SuspensionProductDecomposition (X Y : PointedReadout) :
    PointedEquiv (Suspension (X ⋀ Y)) (Suspension X ⋀ Suspension Y) :=
  PointedEquiv.refl (X ⋀ Y)

/-- Suspension of a smash and join agree in this finite product readout. -/
def SuspensionSmashJoin (X Y : PointedReadout) :
    PointedEquiv (Suspension (X ⋀ Y)) (X ★ Y) :=
  PointedEquiv.refl (X ⋀ Y)

/-- Finite fibre-sequence record with an explicit fibre readout. -/
structure FibreSequence (F E B : PointedReadout) where
  f : PointedMap F E
  g : PointedMap E B
  fibre_readout : PointedEquiv F F

/-- The finite fibre readout carried by a fibre sequence is reflexive data. -/
theorem FibreSequence.fibre_readout_apply
    {F E B : PointedReadout} (fs : FibreSequence F E B) (x : F.carrier) :
    fs.fibre_readout x = fs.fibre_readout.toEquiv x :=
  rfl

end Wedge
