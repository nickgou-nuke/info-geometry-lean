import InfoGeometry.Canonical.SplitCliffordSourceCurrentTransport
import InfoGeometry.Canonical.SplitCliffordSourceWittFock

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCl44ClosureTarget

Concrete closure target for the split-current corridor over a real `Cl(4,4)`
split-Witt realization.

This file does not fake closure. It records exactly the remaining theorem debt:

1. construct `Jlift : Int → V →ₗ[𝕜] V`;
2. prove finite-support action lemmas for the concrete split-Witt realization;
3. prove `truncLift`;
4. prove `wickLift`;
5. package through `packagedHeisenbergWitness`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordSourceCl44ClosureTarget

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCarrier
open InfoGeometry.Canonical.SplitCliffordSourceCurrent
open InfoGeometry.Canonical.SplitCliffordSourceCurrentTransport
open InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
open InfoGeometry.Canonical.SplitCliffordSourceWittFock

/--
Marker surface for a concrete real `Cl(4,4)` split-Witt source realization.

This is intentionally minimal: it names the owner branch where the concrete
Witt data and CAR/Wick lemmas will be supplied.
-/
structure RealCl44SplitWittDatum
    (𝕜 V Carrier : Type*)
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (S : SplitSourceCarrier 𝕜 V Carrier)
    (Jsrc : SplitSourceCurrent 𝕜 V Carrier S) where
  /-- Concrete transported mode family to be constructed from split-Witt data. -/
  Jlift : Int → V →ₗ[𝕜] V
  /-- Transport compatibility with the carrier-valued source current. -/
  transported :
    ∀ n : Int, ∀ v : V,
      S.embed (Jlift n v) = Jsrc.modeAction n v

variable {𝕜 V Carrier : Type*}
variable [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup Carrier] [Module 𝕜 Carrier]
variable {S : SplitSourceCarrier 𝕜 V Carrier}
variable {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}

/--
Concrete theorem debt #1:
finite-support action for the real `Cl(4,4)` split-Witt realization.
-/
theorem finiteSupportAction_from_realCl44
    (W : SplitCliffordSourceWittFock.WittGenerators 𝕜 V)
    (P : SplitCliffordSourceWittFock.WittGenerators.DiracPolarization) :
    ∀ n : Int, ∀ v : V,
      SplitCliffordSourceWittFock.WittGenerators.IsFinitelySupportedCurrentAction W P n v := by
  sorry

/--
Concrete theorem debt #2:
from real `Cl(4,4)` split-Witt data, prove truncation of lifted modes.
-/
theorem truncLift_from_realCl44
    (D : RealCl44SplitWittDatum 𝕜 V Carrier S Jsrc) :
    ∀ v : V, ∀ᶠ n : Int in atTop, D.Jlift n v = 0 := by
  sorry

/--
Concrete theorem debt #3:
from real `Cl(4,4)` split-Witt data, prove the Wick/Heisenberg commutator.
-/
theorem wickLift_from_realCl44
    (D : RealCl44SplitWittDatum 𝕜 V Carrier S Jsrc) :
    ∀ m n : Int,
      (D.Jlift m).commutator (D.Jlift n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0 := by
  sorry

/--
Assemble `SplitCurrentEndTransport` once concrete truncation and Wick debts are
discharged.
-/
def transport_from_realCl44
    (D : RealCl44SplitWittDatum 𝕜 V Carrier S Jsrc) :
    SplitCurrentEndTransport S Jsrc where
  Jlift := D.Jlift
  transported := D.transported
  truncLift := truncLift_from_realCl44 D
  wickLift := wickLift_from_realCl44 D

/--
Concrete closure target:
package a real `Cl(4,4)` split-Witt transport into a strict Heisenberg witness.
-/
def packagedHeisenbergWitness_from_realCl44
    (D : RealCl44SplitWittDatum 𝕜 V Carrier S Jsrc) :
    InfoGeometry.Canonical.SplitCliffordHeisenbergBridge.SplitCliffordHeisenbergWitness 𝕜 V :=
  SplitCurrentEndTransport.toHeisenbergWitness (transport_from_realCl44 D)

end InfoGeometry.Canonical.SplitCliffordSourceCl44ClosureTarget
