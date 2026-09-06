import InfoGeometry.Spectral.Homotopy.Suspension

/-!
# Pointed products

The old `cogroup` reference begins with the product universal property for
pointed maps.  This is the carrier-level Lean 4 port of that portion; the
unreduced wedge/co-H-space laws remain separate from this elementary fact.
-/

noncomputable section

namespace InfoGeometry.Spectral.Homotopy.Cogroup

open InfoGeometry.Spectral.Homotopy.Suspension

def pair {X Y Z : PointedReadout} (f : PointedMap X Y) (g : PointedMap X Z) :
    PointedMap X { carrier := Y.carrier × Z.carrier, base := (Y.base, Z.base) } where
  toFun x := (f x, g x)
  map_base := by
    change (f X.base, g X.base) = (Y.base, Z.base)
    exact Prod.ext f.map_base g.map_base

def fst {X Y : PointedReadout} :
    PointedMap { carrier := X.carrier × Y.carrier, base := (X.base, Y.base) } X where
  toFun := Prod.fst
  map_base := rfl

def snd {X Y : PointedReadout} :
    PointedMap { carrier := X.carrier × Y.carrier, base := (X.base, Y.base) } Y where
  toFun := Prod.snd
  map_base := rfl

def prodEquiv (X Y Z : PointedReadout) :
    PointedEquiv
      { carrier := X.carrier → (Y.carrier × Z.carrier),
        base := fun _ => (Y.base, Z.base) }
      { carrier := (X.carrier → Y.carrier) × (X.carrier → Z.carrier),
        base := (fun _ => Y.base, fun _ => Z.base) } where
  toEquiv :=
    { toFun := fun f => (fun x => (f x).1, fun x => (f x).2)
      invFun := fun fg x => (fg.1 x, fg.2 x)
      left_inv := by intro f; funext x; rfl
      right_inv := by intro fg; cases fg; rfl }
  map_base := rfl

@[simp] theorem pair_apply {X Y Z : PointedReadout}
    (f : PointedMap X Y) (g : PointedMap X Z) (x : X.carrier) :
    pair f g x = (f x, g x) := rfl

@[simp] theorem fst_apply {X Y : PointedReadout} (x : X.carrier × Y.carrier) :
    fst (X := X) (Y := Y) x = x.1 := rfl

@[simp] theorem snd_apply {X Y : PointedReadout} (x : X.carrier × Y.carrier) :
    snd (X := X) (Y := Y) x = x.2 := rfl

end InfoGeometry.Spectral.Homotopy.Cogroup
