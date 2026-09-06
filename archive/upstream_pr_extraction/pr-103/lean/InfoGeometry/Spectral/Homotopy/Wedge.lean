import Mathlib.Tactic
import InfoGeometry.Spectral.Homotopy.Smash

/-!
# Finite wedge and join readouts

This is a theorem-safe finite replacement for the old unstable homotopy
skeleton.  Wedge is represented by a sum carrier and join by a product carrier;
only the corresponding elementary equivalences are proved.
-/

noncomputable section

namespace InfoGeometry.Spectral.Homotopy.Wedge

open InfoGeometry.Spectral.Homotopy.Suspension
open InfoGeometry.Spectral.Homotopy.Smash

/-- Finite pointed wedge readout, represented by a sum carrier. -/
def WedgeSum (X Y : PointedReadout) : PointedReadout :=
  Pointed.mk (X.carrier ⊕ Y.carrier) (Sum.inl X.base)

infixr:65 " ⋁ " => WedgeSum

/-- Functoriality of the finite wedge readout. -/
def WedgeSum.map {X Y Z W : PointedReadout}
    (f : PointedMap X Y) (g : PointedMap Z W) :
    PointedMap (X ⋁ Z) (Y ⋁ W) where
  toFun := Sum.elim (fun x => Sum.inl (f x)) (fun z => Sum.inr (g z))
  map_base := by
    exact congrArg Sum.inl f.map_base

@[simp]
theorem WedgeSum_map_apply {X Y Z W : PointedReadout}
    (f : PointedMap X Y) (g : PointedMap Z W) (x : (X ⋁ Z).carrier) :
    WedgeSum.map f g x = Sum.elim (fun a => Sum.inl (f a)) (fun b => Sum.inr (g b)) x :=
  rfl

@[simp]
theorem WedgeSum.map_id (X Z : PointedReadout) :
    WedgeSum.map (PointedMap.id X) (PointedMap.id Z) =
      PointedMap.id (X ⋁ Z) := by
  apply PointedMap.ext
  intro x
  cases x <;> rfl

theorem WedgeSum.map_comp
    {X Y Y' Z W W' : PointedReadout}
    (f : PointedMap X Y) (f' : PointedMap Y Y')
    (g : PointedMap Z W) (g' : PointedMap W W') :
    WedgeSum.map (PointedMap.comp f' f) (PointedMap.comp g' g) =
      PointedMap.comp (WedgeSum.map f' g') (WedgeSum.map f g) := by
  apply PointedMap.ext
  intro x
  cases x <;> rfl

/-- The finite wedge has the expected eliminator for pointed maps. -/
def WedgeSum.lift {X Y Z : PointedReadout}
    (f : PointedMap X Z) (g : PointedMap Y Z) :
    PointedMap (X ⋁ Y) Z where
  toFun := Sum.elim f g
  map_base := f.map_base

@[simp]
theorem WedgeSum.lift_inl {X Y Z : PointedReadout}
    (f : PointedMap X Z) (g : PointedMap Y Z) (x : X.carrier) :
    WedgeSum.lift f g (Sum.inl x) = f x :=
  rfl

@[simp]
theorem WedgeSum.lift_inr {X Y Z : PointedReadout}
    (f : PointedMap X Z) (g : PointedMap Y Z) (y : Y.carrier) :
    WedgeSum.lift f g (Sum.inr y) = g y :=
  rfl

theorem WedgeSum.lift_unique {X Y Z : PointedReadout}
    (f : PointedMap X Z) (g : PointedMap Y Z)
    (h : PointedMap (X ⋁ Y) Z)
    (hinl : ∀ x, h (Sum.inl x) = f x)
    (hinr : ∀ y, h (Sum.inr y) = g y) :
    h = WedgeSum.lift f g := by
  apply PointedMap.ext
  intro x
  cases x with
  | inl x => exact hinl x
  | inr y => exact hinr y

/-- Finite pointed join readout, represented here by a product carrier. -/
def Join (X Y : PointedReadout) : PointedReadout :=
  Pointed.mk (X.carrier × Y.carrier) (X.base, Y.base)

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

end InfoGeometry.Spectral.Homotopy.Wedge
