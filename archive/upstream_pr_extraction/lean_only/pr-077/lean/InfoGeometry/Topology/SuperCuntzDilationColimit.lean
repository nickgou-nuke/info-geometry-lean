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

namespace InfoGeometry.Topology.SuperCuntzDilationColimit

open InfoGeometry.Canonical.ErlangenInductiveClosure
open InfoGeometry.Canonical.ErlangenColimitResolution

variable (Chain : ℕ → Type*) [∀ n : ℕ, Ring (Chain n)]

/-! The q-dilation corridor is already a direct-limit tower on the invariant
packet.  This file keeps only the honest transport surface into that tower. -/
def qDilationColimitResolution
    (Invariants : ∀ n : ℕ, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n : ℕ, BondingIntertwiner (Invariants n) (Invariants (n + 1)))
    :
    ColimitInheritsInvariants Chain Invariants Bonding :=
  ColimitInheritsInvariants.fromStages Chain Invariants Bonding

/-- The colimit transport is exactly the direct-limit invariant packet. -/
theorem qDilationColimitResolution_eq_fromStages
    (Invariants : ∀ n : ℕ, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n : ℕ, BondingIntertwiner (Invariants n) (Invariants (n + 1))) :
    qDilationColimitResolution (Chain := Chain) Invariants Bonding =
      ColimitInheritsInvariants.fromStages Chain Invariants Bonding :=
  rfl

end InfoGeometry.Topology.SuperCuntzDilationColimit
