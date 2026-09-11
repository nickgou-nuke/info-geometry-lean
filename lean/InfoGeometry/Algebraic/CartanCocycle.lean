/-
InfoGeometry/Algebraic/CartanCocycle.lean

Generic Cartan cocycle and automorphy-factor readout for the higher-rank
split lanes.
No complex imports.
-/
import Paperproof
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import InfoGeometry.Algebraic.SplitQuadraticForm
import InfoGeometry.Geometry.RealSiegelSpace

noncomputable section

namespace InfoGeometry.Algebraic.Cartan

open InfoGeometry.Geometry.Cartan

/--
A generic Cartan automorphy factor valued in a monoid.

This is the higher-rank analogue of a scalar denominator or matrix factor.
-/
structure CartanAutomorphyFactor
    (G X A : Type*)
    [Group G] [MulAction G X] [Monoid A] where
  toFun : G → X → A
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ g h x, toFun (g * h) x = toFun g (h • x) * toFun h x

instance
    {G X A : Type*}
    [Group G] [MulAction G X] [Monoid A] :
    CoeFun (CartanAutomorphyFactor G X A) (fun _ => G → X → A) where
  coe J := J.toFun

namespace CartanAutomorphyFactor

variable
    {G H X A : Type*}
    [Group G] [Group H]
    [MulAction G X] [MulAction H X]
    [Monoid A]

/--
Pull back a Cartan automorphy factor along a group homomorphism, provided the
two actions agree through that homomorphism.
-/
def pullback
    (J : CartanAutomorphyFactor H X A)
    (φ : G →* H)
    (hsmul : ∀ (g : G) (x : X), φ g • x = g • x) :
    CartanAutomorphyFactor G X A where
  toFun g x := J (φ g) x
  map_one x := by
    simpa using J.map_one x
  map_mul g h x := by
    rw [φ.map_mul]
    rw [J.map_mul (φ g) (φ h) x]
    rw [hsmul h x]

end CartanAutomorphyFactor

/--
A Cartan rotor cocycle obtained from an automorphy factor and a rotor readout.
-/
structure CartanRotorCocycle
    (G X R : Type*)
    [Group G] [MulAction G X] [Monoid R] where
  toFun : G → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ g h x, toFun (g * h) x = toFun g (h • x) * toFun h x

instance
    {G X R : Type*}
    [Group G] [MulAction G X] [Monoid R] :
    CoeFun (CartanRotorCocycle G X R) (fun _ => G → X → R) where
  coe C := C.toFun

namespace CartanRotorCocycle

variable
    {G X R : Type*}
    [Group G] [MulAction G X] [Monoid R]

/--
Convert a Cartan automorphy factor into a rotor cocycle through a monoid
homomorphism.
-/
def toRotorCocycle
    {A : Type*}
    [Monoid A]
    (J : CartanAutomorphyFactor G X A)
    (weightReadout : A →* R) :
    CartanRotorCocycle G X R where
  toFun g x := weightReadout (J g x)
  map_one x := by
    rw [J.map_one x]
    exact weightReadout.map_one
  map_mul g h x := by
    rw [J.map_mul g h x]
    exact weightReadout.map_mul _ _

/--
On any subgroup whose projected action fixes a point, the cocycle collapses to
a strict group homomorphism.
-/
def stabilizerHom
    (C : CartanRotorCocycle G X R)
    (x : X)
    (H : Subgroup G)
    (hH : ∀ g ∈ H, g • x = x) :
    H →* R where
  toFun γ := C (γ : G) x
  map_one' := by
    simpa using C.map_one x
  map_mul' γ δ := by
    have hδ : (δ : G) • x = x := hH δ δ.property
    simpa [hδ] using C.map_mul (γ : G) (δ : G) x

end CartanRotorCocycle

end InfoGeometry.Algebraic.Cartan
