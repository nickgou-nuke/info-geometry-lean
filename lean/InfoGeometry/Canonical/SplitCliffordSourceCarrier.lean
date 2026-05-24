import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCarrier

Source-carrier interface for split-Clifford current construction.

This file is intentionally abstract. It does not construct current modes.
It records the carrier and stabilization predicates that downstream owner files
must consume to prove truncation/commutator laws.
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

end InfoGeometry.Canonical.SplitCliffordSourceCarrier
