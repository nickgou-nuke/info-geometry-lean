import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/-!
# InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

Heisenberg witness packaging from source-side current obligations.

This file is the last source-side step before the existing
`SplitCliffordHeisenbergBridge` and `CurrentSugawaraBridge`.
It is purely structural: it packages proved source obligations; it does not
prove those obligations from split completion data.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCarrier
open InfoGeometry.Canonical.SplitCliffordSourceCurrent
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

/--
Bundle a supplied endomorphism-valued current witness into the split
Heisenberg bridge type.

This function is intentionally strict: it requires the transported mode family
`Jlift` and its truncation/commutator laws as explicit inputs.
-/
def packagedHeisenbergWitness
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Jlift : Int → V →ₗ[𝕜] V)
    (hTruncLift : ∀ v : V, ∀ᶠ l : Int in atTop, Jlift l v = 0)
    (hCommLift : ∀ m n : Int,
      (Jlift m).commutator (Jlift n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) :
    SplitCliffordHeisenbergWitness 𝕜 V where
  J := Jlift
  trunc := hTruncLift
  comm := hCommLift

end InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
