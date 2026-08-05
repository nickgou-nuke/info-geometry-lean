import Mathlib.Tactic
import InfoGeometry.Spectral.Homotopy.Suspension

/-!
# Finite smash-product readouts

The old port named several unstable homotopy equivalences that are not supplied
by this repository.  This file provides finite product readouts and proves only
the product equivalences that are actually represented here.
-/

noncomputable section

namespace InfoGeometry.Spectral.Homotopy.Smash

open InfoGeometry.Spectral.Homotopy.Suspension

/-- Finite pointed smash readout, represented by product of carriers. -/
def SmashProduct (X Y : PointedReadout) : PointedReadout :=
  Pointed.mk (X.carrier × Y.carrier) (X.base, Y.base)

infixr:70 " ⋀ " => SmashProduct

/-- Functoriality of the finite smash readout. -/
def SmashProduct.map {X Y Z W : PointedReadout}
    (f : PointedMap X Y) (g : PointedMap Z W) :
    PointedMap (X ⋀ Z) (Y ⋀ W) where
  toFun x := (f x.1, g x.2)
  map_base := by
    exact Prod.ext f.map_base g.map_base

@[simp]
theorem SmashProduct_map_apply {X Y Z W : PointedReadout}
    (f : PointedMap X Y) (g : PointedMap Z W) (x : (X ⋀ Z).carrier) :
    SmashProduct.map f g x = (f x.1, g x.2) :=
  rfl

/-- Product associativity as a pointed equivalence. -/
def SmashProduct.assoc (X Y Z : PointedReadout) :
    PointedEquiv ((X ⋀ Y) ⋀ Z) (X ⋀ (Y ⋀ Z)) where
  toEquiv :=
    { toFun := fun x => (x.1.1, (x.1.2, x.2))
      invFun := fun x => ((x.1, x.2.1), x.2.2)
      left_inv := by intro x; cases x with | mk xy z => cases xy; rfl
      right_inv := by intro x; cases x with | mk x yz => cases yz; rfl }
  map_base := rfl

/-- Product commutativity as a pointed equivalence. -/
def SmashProduct.comm (X Y : PointedReadout) :
    PointedEquiv (X ⋀ Y) (Y ⋀ X) where
  toEquiv := Equiv.prodComm X.carrier Y.carrier
  map_base := rfl

/-- In the finite readout layer, suspension of a product is the same product. -/
def SmashSuspensionReadout (X Y : PointedReadout) :
    PointedEquiv (Suspension (X ⋀ Y)) (Suspension X ⋀ Y) :=
  PointedEquiv.refl (X ⋀ Y)

/-- In the finite readout layer, loops of a product are the same product. -/
def SmashLoopReadout (X Y : PointedReadout) :
    PointedEquiv (LoopSpace (X ⋀ Y)) (X ⋀ LoopSpace Y) :=
  PointedEquiv.refl (X ⋀ Y)

/-- Product readout for two split-Clifford finite stages. -/
def SplitCliffordSmash (n m : ℕ) : PointedReadout :=
  SplitCliffordSuspension n ⋀ SplitCliffordSuspension m

@[simp]
theorem SplitCliffordSmash_base (n m : ℕ) :
    (SplitCliffordSmash n m).base =
      ((SplitCliffordSuspension n).base, (SplitCliffordSuspension m).base) :=
  rfl

/-- Suspension-product readout at the finite carrier level. -/
def SuspensionProductReadout (X Y : PointedReadout) :
    PointedEquiv (Suspension (X ⋀ Y)) (Suspension X ⋀ Suspension Y) :=
  PointedEquiv.refl (X ⋀ Y)

end InfoGeometry.Spectral.Homotopy.Smash
