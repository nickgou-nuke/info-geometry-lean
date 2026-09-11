import InfoGeometry.Spectral.Homotopy.Suspension
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ordinary pointed homotopies

The legacy source uses HoTT's pointed homotopy records.  This owner exposes
the kernel-native part of that interface: pointwise equality of
basepoint-preserving maps.  It deliberately does not claim a topological
path-space or univalence interpretation.
-/

namespace InfoGeometry.Spectral.Homotopy.Pointed

open InfoGeometry.Spectral.Homotopy.Suspension

universe u v

abbrev Homotopy {X Y : PointedReadout} (f g : PointedMap X Y) : Prop :=
  ∀ x, f x = g x

theorem Homotopy.refl {X Y : PointedReadout} (f : PointedMap X Y) :
    Homotopy f f := by
  intro x
  rfl

theorem Homotopy.symm {X Y : PointedReadout} {f g : PointedMap X Y}
    (h : Homotopy f g) : Homotopy g f := by
  intro x
  exact (h x).symm

theorem Homotopy.trans {X Y : PointedReadout} {f g h : PointedMap X Y}
    (hfg : Homotopy f g) (hgh : Homotopy g h) : Homotopy f h := by
  intro x
  exact (hfg x).trans (hgh x)

theorem comp_left {X Y Z : PointedReadout} {f g : PointedMap X Y}
    (k : PointedMap Y Z) (h : Homotopy f g) :
    Homotopy (PointedMap.comp k f) (PointedMap.comp k g) := by
  intro x
  exact congrArg k (h x)

theorem comp_right {X Y Z : PointedReadout} (h : PointedMap Y Z)
    {f g : PointedMap X Y} (p : Homotopy f g) :
    Homotopy (PointedMap.comp h f) (PointedMap.comp h g) := by
  exact comp_left h p

theorem precomp {W X Y : PointedReadout} (k : PointedMap W X)
    {f g : PointedMap X Y} (p : Homotopy f g) :
    Homotopy (PointedMap.comp f k) (PointedMap.comp g k) := by
  intro x
  exact p (k x)

end InfoGeometry.Spectral.Homotopy.Pointed
