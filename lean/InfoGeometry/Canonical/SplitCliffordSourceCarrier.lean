import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCarrier

Source-carrier interface for split-Clifford current construction.

This file is intentionally abstract. It does not construct current modes.
It records the carrier and stabilization predicates that downstream owner files
must consume to prove truncation/commutator laws.

The monotonicity field is part of the theorem-facing boundary: an existential
cutoff can only be promoted cleanly to an `atTop` eventual statement when the
cutoff predicate is upward closed.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceCarrier

open Filter

/--
Abstract split source carrier with a mode-indexed stabilization witness.

`stableCutoff v N` should mean: for the source vector `v`, all sufficiently
large modes are inactive beyond cutoff `N`.
-/
structure SplitSourceCarrier
    (𝕜 V Carrier : Type*) [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier] where
  /-- Embed source vectors into the carrier. -/
  embed : V →ₗ[𝕜] Carrier
  /-- Source-side stabilization cutoff predicate. -/
  stableCutoff : V → Int → Prop
  /-- Every source vector has some stabilization cutoff. -/
  exists_stableCutoff : ∀ v : V, ∃ N : Int, stableCutoff v N
  /-- Stabilization persists after increasing the cutoff. -/
  stableCutoff_mono :
    ∀ {v : V} {N M : Int},
      stableCutoff v N → N ≤ M → stableCutoff v M

namespace SplitSourceCarrier

variable {𝕜 V Carrier : Type*} [Field 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup Carrier] [Module 𝕜 Carrier]

/-- Re-export of cutoff monotonicity. -/
theorem stableCutoff_of_le
    (S : SplitSourceCarrier 𝕜 V Carrier)
    {v : V} {N M : Int}
    (hN : S.stableCutoff v N) (hNM : N ≤ M) :
    S.stableCutoff v M :=
  S.stableCutoff_mono hN hNM

/--
Existence plus monotonicity gives the filter-facing eventual stabilization
statement used by source-current truncation proofs.
-/
theorem eventually_stableCutoff
    (S : SplitSourceCarrier 𝕜 V Carrier)
    (v : V) :
    ∀ᶠ M : Int in atTop, S.stableCutoff v M := by
  rcases S.exists_stableCutoff v with ⟨N, hN⟩
  exact eventually_atTop.2 ⟨N, fun M hNM => S.stableCutoff_mono hN hNM⟩

end SplitSourceCarrier

end InfoGeometry.Canonical.SplitCliffordSourceCarrier
