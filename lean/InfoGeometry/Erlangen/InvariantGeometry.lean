import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Erlangen invariant geometry

This file records the minimal Lean vocabulary for the Erlangen principle:
geometric structure is expressed as invariance under an already-installed
action.

There is deliberately no wrapper structure carrying an action field and no
modular-flow witness.  The group action is the ordinary mathlib `MulAction`
typeclass, and the Lie action is the ordinary mathlib Lie-module bracket.
Every theorem below is just an unpacking of those action interfaces.
-/

namespace InfoGeometry.Erlangen.InvariantGeometry

/-! ## Group-action invariants -/

section GroupAction

variable (G M : Type*) [Group G] [MulAction G M]

/-- A point fixed by the whole group action. -/
def IsFixedPoint (x : M) : Prop :=
  ∀ g : G, g • x = x

/-- A predicate invariant under the group action. -/
def IsGeometricInvariant (P : M → Prop) : Prop :=
  ∀ (g : G) (x : M), P (g • x) ↔ P x

/-- A readout/function invariant under the group action. -/
def IsInvariantReadout {β : Type*} (f : M → β) : Prop :=
  ∀ (g : G) (x : M), f (g • x) = f x

/-- A map intertwines two already-installed group actions. -/
def IsEquivariantMap
    {N : Type*} [MulAction G N] (f : M → N) : Prop :=
  ∀ (g : G) (x : M), f (g • x) = g • f x

variable {G M}

/-- The fixed-point predicate is exactly its defining fixedness law. -/
theorem fixedPoint_apply {x : M} (hx : IsFixedPoint G M x) (g : G) :
    g • x = x :=
  hx g

/-- Invariant predicates may be read after acting by a group element. -/
theorem invariantPredicate_apply
    {P : M → Prop} (hP : IsGeometricInvariant G M P) (g : G) (x : M) :
    P (g • x) ↔ P x :=
  hP g x

/-- Alias with the geometric-invariant name used by downstream Erlangen modules. -/
theorem geometricInvariant_iff
    {P : M → Prop} (hP : IsGeometricInvariant G M P) (g : G) (x : M) :
    P (g • x) ↔ P x :=
  hP g x

/-- Invariant readouts are constant along group orbits. -/
theorem invariantReadout_apply
    {β : Type*} {f : M → β} (hf : IsInvariantReadout G M f) (g : G) (x : M) :
    f (g • x) = f x :=
  hf g x

/-- Equivariant maps commute with the two group actions. -/
theorem equivariantMap_apply
    {N : Type*} [MulAction G N] {f : M → N}
    (hf : IsEquivariantMap G M f) (g : G) (x : M) :
    f (g • x) = g • f x :=
  hf g x

/--
An invariant predicate has the same truth value on any element of a displayed
orbit relation.
-/
theorem invariantPredicate_of_eq_smul
    {P : M → Prop} (hP : IsGeometricInvariant G M P)
    {x y : M} (g : G) (hy : y = g • x) :
    P y ↔ P x := by
  subst y
  exact hP g x

/--
An invariant readout has the same value on any element of a displayed orbit
relation.
-/
theorem invariantReadout_of_eq_smul
    {β : Type*} {f : M → β} (hf : IsInvariantReadout G M f)
    {x y : M} (g : G) (hy : y = g • x) :
    f y = f x := by
  subst y
  exact hf g x

end GroupAction

/-! ## Lie-action invariants / Casimirs -/

section LieAction

variable (L M : Type*)
variable [LieRing L] [AddCommGroup M] [LieRingModule L M]

/--
A vector fixed infinitesimally by an already-installed Lie action.

This is the Lean-safe Casimir/invariant predicate for a module carrying a
mathlib Lie-module structure.  It does not install an action as a field.
-/
def IsLieInvariant (m : M) : Prop :=
  ∀ X : L, ⁅X, m⁆ = 0

/--
Casimir vocabulary for an associative algebra carrying an already-installed
Lie-module action.
-/
abbrev IsCasimir (C : M) : Prop :=
  IsLieInvariant L M C

variable {L M}

/-- A Lie invariant is annihilated by every infinitesimal generator. -/
theorem lieInvariant_apply {m : M}
    (hm : IsLieInvariant L M m) (X : L) :
    ⁅X, m⁆ = 0 :=
  hm X

/-- A Casimir is annihilated by every infinitesimal generator. -/
theorem casimir_fixed_by_generator {C : M}
    (hC : IsCasimir L M C) (X : L) :
    ⁅X, C⁆ = 0 :=
  hC X

end LieAction

/-! ## Explicit linear-action predicates -/

section ExplicitLinearAction

variable (R L M : Type*)
variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

/--
Casimir vocabulary for a displayed infinitesimal linear action.

This is still only a predicate.  The linear map is an explicit parameter, not a
stored field of a geometry structure.  Downstream modules should instantiate it
from an already-owned representation or a mathlib construction.
-/
def IsCasimirForAction (action : L →ₗ[R] Module.End R M) (C : M) : Prop :=
  ∀ X : L, action X C = 0

variable {R L M}

/-- A Casimir for a displayed linear action is annihilated by every generator. -/
theorem casimir_action_eq_zero
    {action : L →ₗ[R] Module.End R M} {C : M}
    (hC : IsCasimirForAction R L M action C) (X : L) :
    action X C = 0 :=
  hC X

end ExplicitLinearAction

end InfoGeometry.Erlangen.InvariantGeometry
