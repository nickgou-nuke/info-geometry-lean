/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.SuperCuntzDilationCurvature
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ErlangenColimitResolution

/-!
# Super-Cuntz Dilation Colimit Bridge

This file does not claim a new analytic `O_{N|M}(q)` theory or a continuum
curvature theorem.  It packages the existing finite q-dilation corridor as a
stagewise family and routes the invariant transport through the repository's
inductive-colimit owner.

The point is structural:

- the finite q-supergrading / modular-dilation / q-deficit readouts remain in
  `SuperCuntzDilationCurvature`;
- the stagewise invariant packets are then transported through
  `Canonical.ErlangenColimitResolution`.

So the `n`-dependent corridor is represented as a genuine inductive-colimit
surface instead of a one-off finite packet.
-/

namespace InfoGeometry.Topology.SuperCuntzDilationColimit

universe u

open InfoGeometry.Canonical.ErlangenInductiveClosure
open InfoGeometry.Canonical.ErlangenColimitResolution

variable (Chain : ℕ → Type u) [∀ n : ℕ, Ring (Chain n)]

/-- The stagewise q-dilation invariants and the induced map into a compatible
ambient algebra.  Cone compatibility is explicit because stage maps alone do
not define a map out of the colimit. -/
noncomputable def qDilationColimitResolution
    (Invariants : ∀ n : ℕ, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n : ℕ, BondingIntertwiner (Invariants n) (Invariants (n + 1)))
    (A_infty : Type u) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n : ℕ, BondingIntertwiner (Invariants n) GlobalInvariants)
    (global_compatible : ∀ n x,
      (global_embed (n + 1)).map ((Bonding n).map x) = (global_embed n).map x) :
    ColimitInheritsInvariants Chain Invariants Bonding ×
      (ColimitInheritsInvariants.ColimitStage Chain Invariants Bonding →+* A_infty) :=
  resolveColimitInheritsInvariants_of_ambient
    (Chain := Chain) (Invariants := Invariants) (Bonding := Bonding)
    (A_infty := A_infty) (GlobalInvariants := GlobalInvariants)
    global_embed global_compatible

end InfoGeometry.Topology.SuperCuntzDilationColimit

