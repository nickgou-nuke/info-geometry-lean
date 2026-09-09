import InfoGeometry.Spectral.Homotopy.Suspension

/-!
# Binary pointed maps

This is the ordinary pointed-set portion of the old `pointed_binary` file.
Higher homotopy coherence is intentionally outside this finite readout layer.
-/

namespace InfoGeometry.Spectral.Homotopy.BinaryMap

open InfoGeometry.Spectral.Homotopy.Suspension

structure BinaryPointedMap (X Y Z : PointedReadout) where
  toFun : X.carrier → Y.carrier → Z.carrier
  map_base_left : ∀ y, toFun X.base y = Z.base
  map_base_right : ∀ x, toFun x Y.base = Z.base

instance {X Y Z : PointedReadout} : CoeFun (BinaryPointedMap X Y Z)
    (fun _ => X.carrier → Y.carrier → Z.carrier) where
  coe f := f.toFun

def productPointed (X Y : PointedReadout) : PointedReadout where
  carrier := X.carrier × Y.carrier
  base := (X.base, Y.base)

@[simp] theorem map_base_left_apply {X Y Z : PointedReadout}
    (f : BinaryPointedMap X Y Z) (y : Y.carrier) :
    f X.base y = Z.base :=
  f.map_base_left y

@[simp] theorem map_base_right_apply {X Y Z : PointedReadout}
    (f : BinaryPointedMap X Y Z) (x : X.carrier) :
    f x Y.base = Z.base :=
  f.map_base_right x

def toPointedMap {X Y Z : PointedReadout} (f : BinaryPointedMap X Y Z) :
    PointedMap (productPointed X Y) Z where
  toFun := fun p => f p.1 p.2
  map_base := by
    change f X.base Y.base = Z.base
    exact f.map_base_left Y.base

@[simp] theorem toPointedMap_apply {X Y Z : PointedReadout}
    (f : BinaryPointedMap X Y Z) (p : X.carrier × Y.carrier) :
    toPointedMap f p = f p.1 p.2 :=
  rfl

def const (X Y Z : PointedReadout) : BinaryPointedMap X Y Z where
  toFun := fun _ _ => Z.base
  map_base_left := fun _ => rfl
  map_base_right := fun _ => rfl

@[simp] theorem const_apply (X Y Z : PointedReadout)
    (x : X.carrier) (y : Y.carrier) :
    const X Y Z x y = Z.base :=
  rfl

end InfoGeometry.Spectral.Homotopy.BinaryMap
