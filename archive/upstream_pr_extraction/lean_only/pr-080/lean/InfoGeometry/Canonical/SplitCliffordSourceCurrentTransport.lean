import InfoGeometry.Canonical.SplitCliffordSourceCurrent
import InfoGeometry.Canonical.SplitCliffordSourceWittFock
import InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordSourceCurrentTransport

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCarrier
open InfoGeometry.Canonical.SplitCliffordSourceCurrent
open InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

structure SplitCurrentEndTransport
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (S : SplitSourceCarrier 𝕜 V Carrier)
    (Jsrc : SplitSourceCurrent 𝕜 V Carrier S) where
  Jlift : Int → V →ₗ[𝕜] V
  transported :
    ∀ n : Int, ∀ v : V,
      S.embed (Jlift n v) = Jsrc n v
  truncLift :
    ∀ v : V, ∀ᶠ n : Int in atTop, Jlift n v = 0
  wickLift :
    ∀ m n : Int,
      (Jlift m).commutator (Jlift n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

namespace SplitCurrentEndTransport

variable {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup Carrier] [Module 𝕜 Carrier]
variable {S : SplitSourceCarrier 𝕜 V Carrier}
variable {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}

def toCurrentHeisenbergRep
    (T : SplitCurrentEndTransport S Jsrc) :
    InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep 𝕜 V :=
  { J := T.Jlift, trunc := T.truncLift, comm := T.wickLift }

end SplitCurrentEndTransport

end InfoGeometry.Canonical.SplitCliffordSourceCurrentTransport
