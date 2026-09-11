/-
InfoGeometry/Algebraic/MatrixAutomorphyFactor.lean

Matrix-valued automorphy factors for the higher-rank Cartan towers.
No complex imports.
-/

import InfoGeometry.Algebraic.CartanCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebraic.Cartan

/--
A generic matrix/group-valued automorphy factor over a group action.

This is the higher-rank replacement for a scalar denominator `cτ + d`.
The target `A` may later be instantiated by a matrix group, a metaplectic
cover, a compact Cartan factor, or a Clifford-unit subgroup.
-/
structure MatrixAutomorphyFactor
    (G X A : Type*)
    [Group G] [MulAction G X] [Monoid A] where
  toFun : G → X → A
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ g h x, toFun (g * h) x = toFun g (h • x) * toFun h x

instance
    {G X A : Type*}
    [Group G] [MulAction G X] [Monoid A] :
    CoeFun (MatrixAutomorphyFactor G X A) (fun _ => G → X → A) where
  coe J := J.toFun

namespace MatrixAutomorphyFactor

variable
    {G H X A R : Type*}
    [Group G] [Group H]
    [MulAction G X] [MulAction H X]
    [Monoid A] [Monoid R]

/--
Pull back a matrix automorphy factor along a group homomorphism.

The hypothesis `hsmul` says that the `G`-action is exactly the action induced
from the `H`-action through `φ`.
-/
def pullback
    (J : MatrixAutomorphyFactor H X A)
    (φ : G →* H)
    (hact : ∀ (g : G) (x : X), φ g • x = g • x) :
    MatrixAutomorphyFactor G X A where
  toFun g x := J (φ g) x
  map_one x := by
    simpa using J.map_one x
  map_mul g h x := by
    calc
      J (φ (g * h)) x = J (φ g * φ h) x := by rw [φ.map_mul]
      _ = J (φ g) ((φ h) • x) * J (φ h) x := J.map_mul (φ g) (φ h) x
      _ = J (φ g) (h • x) * J (φ h) x := by
            simp [hact h x]

/--
Convert a matrix automorphy factor into a rotor cocycle through a monoid
homomorphism.
-/
def toRotorCocycle
    (J : MatrixAutomorphyFactor G X A)
    (weightReadout : A →* R) :
    CartanRotorCocycle G X R where
  toFun g x := weightReadout (J g x)
  map_one x := by
    rw [J.map_one x]
    exact weightReadout.map_one
  map_mul g h x := by
    rw [J.map_mul g h x]
    exact weightReadout.map_mul _ _

end MatrixAutomorphyFactor

end InfoGeometry.Algebraic.Cartan
