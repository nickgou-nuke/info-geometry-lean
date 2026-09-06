import InfoGeometry.External.Virasoro.FockSpace
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.BosonFermionFockIntertwiner

Representation-level bosonization boundary.

The finite split `Cl(1,1)` atom is not isomorphic to the Heisenberg or
Virasoro algebras as a raw finite algebra.  This module therefore records only
the structure that is actually needed at the completed/mode-indexed
representation level: a faithful linear current intertwiner from a fermionic
carrier into a bosonic carrier.

This module formalizes that level only.  It does not construct the
normal-ordered fermion current from raw CAR modes.
-/

namespace InfoGeometry.Canonical.BosonFermionFockIntertwiner

open VirasoroProject

section FockLevel

variable {F B : Type*}
variable [AddCommGroup F] [Module ℝ F]
variable [AddCommGroup B] [Module ℝ B]

/-- Linear endomorphisms of a real representation space. -/
abbrev End (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] V

/--
Bosonization data at the level that actually exists in this corridor: a
faithful representation-level current intertwiner.

The Heisenberg law is stored on the bosonic current side.  The source-side
fermionic current law is then transported through the faithful intertwiner; it
is not a raw finite `Cl(1,1)` algebra isomorphism, and it is not a claim that
the two Fock carriers have already been constructed as equivalent objects.
-/
structure FockLevelCurrentIntertwiner where
  toBoson : F →ₗ[ℝ] B
  toBoson_injective : Function.Injective toBoson
  fermionCurrent : ℤ → End F
  bosonCurrent : ℤ → End B
  fermionCentral : End F
  bosonCentral : End B
  current_intertwines :
    ∀ n : ℤ, ∀ v : F,
      toBoson (fermionCurrent n v) = bosonCurrent n (toBoson v)
  central_intertwines :
    ∀ v : F, toBoson (fermionCentral v) = bosonCentral (toBoson v)
  boson_heisenberg_law :
    ∀ m n : ℤ,
      (bosonCurrent m).commutator (bosonCurrent n) =
        if m + n = 0 then (m : ℝ) • bosonCentral else 0

namespace FockLevelCurrentIntertwiner

variable (X : FockLevelCurrentIntertwiner (F := F) (B := B))

/--
The faithful Fock-level intertwiner transports commutators of intertwined
current operators.
-/
@[rep_depth transport]
theorem current_commutator_intertwines (m n : ℤ) (v : F) :
    X.toBoson (((X.fermionCurrent m).commutator (X.fermionCurrent n)) v) =
      ((X.bosonCurrent m).commutator (X.bosonCurrent n)) (X.toBoson v) := by
  simp [LinearMap.commutator, X.current_intertwines]

/--
The source-side fermionic current operators inherit the Heisenberg law from the
bosonic current operators through the faithful Fock-level intertwiner.
-/
@[rep_depth transport]
theorem fermion_heisenberg_law (m n : ℤ) :
    (X.fermionCurrent m).commutator (X.fermionCurrent n) =
      if m + n = 0 then (m : ℝ) • X.fermionCentral else 0 := by
  ext v
  apply X.toBoson_injective
  rw [current_commutator_intertwines (X := X) m n v, X.boson_heisenberg_law m n]
  by_cases h : m + n = 0
  · simp [h, X.central_intertwines]
  · simp [h]

/--
Readback: the map being used is a faithful Fock-level current intertwiner.
-/
@[rep_depth transport]
theorem intertwiner_level :
    Function.Injective X.toBoson :=
  X.toBoson_injective

end FockLevelCurrentIntertwiner

end FockLevel

end InfoGeometry.Canonical.BosonFermionFockIntertwiner
