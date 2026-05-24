import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.SplitCliffordSourceCarrier

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCurrent

Source-side current-mode interface over a split-Clifford carrier.

This file does not claim truncation is already proved from split completion.
It isolates the exact truncation theorem obligation.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceCurrent

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCarrier

/--
Current modes attached to a split source carrier.

`modeAction l v` is the `l`-th current mode applied to source vector `v`.
-/
structure SplitSourceCurrent
    (𝕜 V Carrier : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (S : SplitSourceCarrier 𝕜 V Carrier) where
  /-- Source current mode family. -/
  modeAction : Int → V →ₗ[𝕜] Carrier

/--
Truncation obligation surface for a split source current.

This is the honest theorem target that must be proved from source stabilization
and transported normal ordering.
-/
def SplitCurrentTruncation
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    (J : SplitSourceCurrent 𝕜 V Carrier S) : Prop :=
  ∀ v : V, ∀ᶠ l : Int in atTop, J.modeAction l v = 0

end InfoGeometry.Canonical.SplitCliffordSourceCurrent

