import InfoGeometry.Topology.SuperCuntzDilationCurvature
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

namespace SuperCuntzDilationColimit

open InfoGeometry.Canonical.ErlangenInductiveClosure
open InfoGeometry.Canonical.ErlangenColimitResolution

variable (Chain : ℕ → Type*) [∀ n : ℕ, Ring (Chain n)]

/--
Colimit wrapper for a stagewise q-dilation corridor.

The packet itself stays finite-stage and is supplied externally.  The wrapper
exists so that the `n`-indexed readouts can be routed through the inductive
colimit owner without inventing a parallel infrastructure.
-/
def qDilationColimitResolution
    (Invariants : ∀ n : ℕ, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n : ℕ, BondingIntertwiner (Invariants n) (Invariants (n + 1)))
    (A_infty : Type*) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n : ℕ, BondingIntertwiner (Invariants n) GlobalInvariants) :
    ColimitInheritsInvariants Chain Invariants Bonding :=
  resolveColimitInheritsInvariants_of_ambient
    (Chain := Chain) (Invariants := Invariants) (Bonding := Bonding)
    (A_infty := A_infty) (GlobalInvariants := GlobalInvariants)
    global_embed

end SuperCuntzDilationColimit

