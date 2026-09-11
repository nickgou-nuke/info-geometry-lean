import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Deformation positivity

This module records the minimal cone/dual-cone interface needed for a
variation-theoretic rigidity statement on a network branch.

It does not claim that an `E8` root lattice alone forces a global minimum.
The only theorem proved here is the local readback:

* if the first variation lies in the dual cone, then it is nonnegative on the
  admissible cone.

That is the Lean-safe starting point for any later action-minimization layer.
-/

namespace InfoGeometry.Network

/--
A pointed positivity cone on a real vector space.

The cone structure is intentionally minimal: it records closure under addition
and scaling by nonnegative scalars.  Any `E8`-specific or geometric instance
would be supplied later as a concrete inhabitant of this interface.
-/
structure VertexCone
    (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] where
  carrier : Set V
  zero_mem : 0 ∈ carrier
  add_mem : ∀ {x y : V}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  smul_mem : ∀ {a : R} {x : V}, 0 ≤ a → x ∈ carrier → a • x ∈ carrier

/--
The dual cone of a positivity cone: linear functionals that are nonnegative on
the cone.
-/
def dualCone
    {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V]
    (C : Set V) : Set (V →ₗ[R] R) :=
  {φ | ∀ x, x ∈ C → 0 ≤ φ x}

@[simp]
theorem mem_dualCone_iff
    {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V]
    {C : Set V} {φ : V →ₗ[R] R} :
    φ ∈ dualCone C ↔ ∀ x, x ∈ C → 0 ≤ φ x := Iff.rfl

/--
Local deformation rigidity data.

`firstVariation` is the action derivative on the network's admissible
deformation cone, and `firstVariation_dual` certifies that it lies in the dual
cone.
-/
structure LocalRigidityDatum
    (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] where
  cone : VertexCone R V
  firstVariation : V →ₗ[R] R
  firstVariation_dual : firstVariation ∈ dualCone (R := R) (V := V) cone.carrier

namespace LocalRigidityDatum

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V]

/-- A local admissible deformation is nonnegative under the first variation. -/
theorem local_first_variation_nonnegative
    (D : LocalRigidityDatum R V)
    (ξ : V)
    (hξ : ξ ∈ D.cone.carrier) :
    0 ≤ D.firstVariation ξ :=
  D.firstVariation_dual ξ hξ

end LocalRigidityDatum

end InfoGeometry.Network
