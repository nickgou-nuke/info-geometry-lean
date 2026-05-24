import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.SplitCliffordSourceCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

Wick/Schwinger commutator interface for split source currents.

This file is an owner-surface for the source-side commutator theorem debt.
It does not postulate closure via `True`/placeholder fields.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

open InfoGeometry.Canonical.SplitCliffordSourceCarrier
open InfoGeometry.Canonical.SplitCliffordSourceCurrent

/--
Source-side Wick commutator law for current modes.

This is the exact commutator equation required by the Heisenberg bridge.
-/
def SplitSourceWickLaw
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    (J : SplitSourceCurrent 𝕜 V Carrier S) : Prop :=
  ∀ m n : Int,
    (J.modeAction m).commutator (J.modeAction n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] Carrier) else 0

end InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

