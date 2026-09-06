import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# InfoGeometry.Categorical.ModularDoubledRealHopfFibration

Categorical skeleton for modular doubled-real fibration shadows with twisted
fibers.

The module name keeps the historical `Hopf` label for compatibility, but the
structure below is intentionally more general.  In the two-qubit lane the
honest quaternionic Hopf map is the pre-projective map `S^7 -> HP^1 ~= S^4`
with `S^3` fiber.  After quotienting by global phase, `CP^3 -> S^4` is the
twistor fibration, with projective fiber `CP^1 ~= S^2`, not a Hopf fibration.

This file is finite and structural.  It does not construct the analytic Hopf
map, the twistor fibration, a smooth bundle, or a Grothendieck stack.  It
records the common categorical data needed by those later constructions:

* a total object space and a base readout;
* a modular involution on the total space;
* an induced involution on the base;
* compatibility of projection with the modular twist;
* fibers as dependent subtypes;
* the modular twist as a functor between fiber categories.

Matrix-level doubled-real models are instances of this categorical surface, not
replacements for it.
-/

open CategoryTheory

universe u v

namespace InfoGeometry.Categorical.ModularDoubledRealHopfFibration

/--
Categorical data for a modular doubled-real fibration shadow.

`projection` is the base readout.  `modularTwist` is the total-space
Tomita/Krein-style twist, and `baseTwist` is its induced action on the base.
The compatibility law says the projection is equivariant up to the base twist.
-/
structure ModularDoubledRealHopf where
  Total : Type u
  Base : Type v
  projection : Total → Base
  modularTwist : Total → Total
  baseTwist : Base → Base
  modularTwist_involutive : Function.Involutive modularTwist
  baseTwist_involutive : Function.Involutive baseTwist
  projection_twist : ∀ x : Total, projection (modularTwist x) = baseTwist (projection x)

namespace ModularDoubledRealHopf

variable (F : ModularDoubledRealHopf.{u, v})

/-- The fiber over a base point. -/
def Fiber (b : F.Base) : Type u :=
  { x : F.Total // F.projection x = b }

/-- Membership in the same ordinary fiber. -/
def SameFiber (x y : F.Total) : Prop :=
  F.projection x = F.projection y

theorem sameFiber_refl (x : F.Total) : F.SameFiber x x := rfl

theorem sameFiber_symm {x y : F.Total} (h : F.SameFiber x y) : F.SameFiber y x :=
  h.symm

theorem sameFiber_trans {x y z : F.Total}
    (hxy : F.SameFiber x y) (hyz : F.SameFiber y z) : F.SameFiber x z :=
  hxy.trans hyz

/-- Same-fiber is an equivalence relation. -/
theorem sameFiber_equivalence : Equivalence F.SameFiber where
  refl := F.sameFiber_refl
  symm := by intro x y h; exact F.sameFiber_symm h
  trans := by intro x y z hxy hyz; exact F.sameFiber_trans hxy hyz

/--
Twisted-fiber relation: after applying the modular twist, `x` lands over the
same base point as `y`.
-/
def TwistedSameFiber (x y : F.Total) : Prop :=
  F.projection (F.modularTwist x) = F.projection y

theorem twistedSameFiber_iff_baseTwist (x y : F.Total) :
    F.TwistedSameFiber x y ↔ F.baseTwist (F.projection x) = F.projection y := by
  unfold TwistedSameFiber
  rw [F.projection_twist x]

theorem twistedSameFiber_of_projection_eq_baseTwist {x y : F.Total}
    (h : F.baseTwist (F.projection x) = F.projection y) :
    F.TwistedSameFiber x y := by
  exact (F.twistedSameFiber_iff_baseTwist x y).2 h

theorem twistedSameFiber_twist_left {x y : F.Total} (h : F.SameFiber x y) :
    F.TwistedSameFiber x (F.modularTwist y) := by
  unfold SameFiber at h
  unfold TwistedSameFiber
  rw [F.projection_twist x, F.projection_twist y, h]

/-- The modular twist sends the fiber over `b` to the fiber over `baseTwist b`. -/
def twistFiber (b : F.Base) : F.Fiber b → F.Fiber (F.baseTwist b) :=
  fun x =>
    ⟨F.modularTwist x.1, by
      rw [F.projection_twist x.1, x.2]⟩

@[simp] theorem twistFiber_val (b : F.Base) (x : F.Fiber b) :
    (F.twistFiber b x).1 = F.modularTwist x.1 := rfl

/-- Applying the fiber twist twice returns the original total-space point. -/
theorem twistFiber_twice_value (b : F.Base) (x : F.Fiber b) :
    (F.twistFiber (F.baseTwist b) (F.twistFiber b x)).1 = x.1 :=
  F.modularTwist_involutive x.1

/-- The base of a twice-twisted fiber is the original base. -/
theorem baseTwist_twice (b : F.Base) : F.baseTwist (F.baseTwist b) = b :=
  F.baseTwist_involutive b

/-! ## Discrete fiber categories and twisted-fiber functors -/

/-- Each fiber carries its discrete category of points. -/
instance fiberCategory (b : F.Base) : Category (F.Fiber b) where
  Hom x y := PLift (x = y)
  id x := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- The modular twist is a functor from a fiber to its twisted fiber. -/
def twistFiberFunctor (b : F.Base) : (F.Fiber b) ⥤ (F.Fiber (F.baseTwist b)) where
  obj := F.twistFiber b
  map := by
    intro x y h
    exact ⟨by cases h.down; rfl⟩

@[simp] theorem twistFiberFunctor_obj (b : F.Base) (x : F.Fiber b) :
    (F.twistFiberFunctor b).obj x = F.twistFiber b x := rfl

/--
Object-level involutivity of the twisted-fiber functor.  The target fiber is
indexed by `baseTwist (baseTwist b)`, so the stable statement is on underlying
total points.
-/
theorem twistFiberFunctor_twice_value (b : F.Base) (x : F.Fiber b) :
    ((F.twistFiberFunctor (F.baseTwist b)).obj ((F.twistFiberFunctor b).obj x)).1 = x.1 :=
  F.twistFiber_twice_value b x

/-! ## Doubled-real swap model -/

/-- Doubled-real carrier used by concrete matrix/Krein instances. -/
abbrev Doubled (E : Type u) : Type u :=
  E × E

/-- The Tomita/Krein swap on a doubled carrier. -/
def doubledSwap {E : Type u} : Doubled E → Doubled E :=
  fun x => (x.2, x.1)

theorem doubledSwap_involutive {E : Type u} : Function.Involutive (doubledSwap (E := E)) := by
  intro x
  cases x
  rfl

/--
Constant-base doubled-real fibration.  This is the minimal categorical model
showing that the doubled modular swap is a fiber twist.  Nontrivial base
readouts instantiate the same structure by replacing `Unit` with the chosen
base and supplying `projection_twist`.
-/
def constantBaseDoubledReal (E : Type u) : ModularDoubledRealHopf where
  Total := Doubled E
  Base := PUnit
  projection := fun _ => PUnit.unit
  modularTwist := doubledSwap
  baseTwist := fun b => b
  modularTwist_involutive := doubledSwap_involutive
  baseTwist_involutive := by intro b; cases b; rfl
  projection_twist := by intro x; rfl

theorem constantBaseDoubledReal_twistFiber_twice (E : Type u)
    (x : (constantBaseDoubledReal E).Fiber PUnit.unit) :
    ((constantBaseDoubledReal E).twistFiber PUnit.unit
      ((constantBaseDoubledReal E).twistFiber PUnit.unit x)).1 = x.1 :=
  (constantBaseDoubledReal E).twistFiber_twice_value PUnit.unit x

end ModularDoubledRealHopf

end InfoGeometry.Categorical.ModularDoubledRealHopfFibration
