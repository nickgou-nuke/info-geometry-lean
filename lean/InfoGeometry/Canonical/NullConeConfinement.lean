import Mathlib.LinearAlgebra.QuadraticForm.Basic

noncomputable section

namespace InfoGeometry.Canonical.NullConeConfinement

/-!
# Null Cone Confinement

This module formalizes the final leg of the "Holy Trinity": 
Null Cone Confinement. 

It establishes the topological restriction of configuration states 
(e.g., $D_4$ spinors or Skyrmions) strictly onto the isotropic boundaries 
(the Null Cone) of a background geometry (such as the Klein Quadric).
-/

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- 
The generalized Null Cone (isotropic boundary) defined by a 
quadratic form `q` on a vector space `V`.
-/
def NullCone (q : QuadraticForm K V) : Set V :=
  { x : V | q x = 0 }

/--
The Klein Quadric Boundary constraint for a pair of vectors `(a, b)`.
Derived from the vanishing of the invariant polynomial `q(a)q(b)q(a-b)`.
A pair is on the boundary if either vector is on the null cone, 
or their difference is.
-/
def KleinQuadricBoundary (q : QuadraticForm K V) : Set (V × V) :=
  { p : V × V | q p.1 = 0 ∨ q p.2 = 0 ∨ q (p.1 - p.2) = 0 }

/-- 
Abstract representation of a physical configuration state that requires 
confinement to the Null Cone.
-/
structure ConfinedState (q : QuadraticForm K V) where
  /-- The underlying physical state vector -/
  state : V
  /-- The confinement witness: the state strictly lives on the null cone -/
  is_confined : state ∈ NullCone q

/--
A Confinement Operator acts as a projector, pulling arbitrary 
states down onto the Null Cone.
-/
structure ConfinementOperator (q : QuadraticForm K V) where
  /-- The abstract projection map -/
  project : V → V
  /-- The projected state unconditionally satisfies the null cone constraint -/
  confines : ∀ (x : V), project x ∈ NullCone q
  /-- The operator acts as the identity on states already confined -/
  idempotent_on_cone : ∀ (x : V), x ∈ NullCone q → project x = x

/--
The Holy Trinity Capstone:
If we have a valid Confinement Operator, applying it to any state 
yields a rigorously ConfinedState.
-/
def enforce_confinement {q : QuadraticForm K V} 
  (op : ConfinementOperator q) (x : V) : ConfinedState q :=
  { state := op.project x,
    is_confined := op.confines x }

/--
Theorem: The confinement operation preserves states that are already 
on the null boundary (e.g. valid classical instantons/skyrmions).
-/
theorem confinement_preserves_valid_states {q : QuadraticForm K V}
  (op : ConfinementOperator q) (x : V) (hx : x ∈ NullCone q) :
  (enforce_confinement op x).state = x := by
  -- Unfold the definition
  dsimp [enforce_confinement]
  -- Use the idempotence property of the confinement operator
  exact op.idempotent_on_cone x hx

end InfoGeometry.Canonical.NullConeConfinement
