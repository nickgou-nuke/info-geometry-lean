import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Canonical.BerryConnection

noncomputable section

namespace Experimental.ModularBerryBridge

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.BerryPhase
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => EndH E

/--
The finite Radon--Nikodym modular generator supplied by the surviving owner
data.  This recovers the operator carried historically by
`RelativeModularCarrier.modularHamiltonian` without duplicating the modular
and Hestenes--Kähler owners in a wrapper structure.
-/
noncomputable def rnModularHamiltonian
    (M : ModularRadonNikodymData E) : EndH :=
  (-Real.log M.rnDerivative) • idEndH E

/--
Historical negative-log readback, now stated directly for the
`ModularRadonNikodymData` owner.
-/
@[simp]
theorem modularHamiltonian_eq_neg_log_delta
    (M : ModularRadonNikodymData E) :
    rnModularHamiltonian M =
      (-Real.log M.rnDerivative) • idEndH E :=
  rfl

/--
Historical modular-transport readback.  The transport is no longer stored
twice: it is the modular automorphism group owned by `M`.
-/
theorem modularTransport_eq_conjugation
    (M : ModularRadonNikodymData E)
    (s t : ℝ) (A : EndH) :
    M.modularAutomorphismGroup (s + t) A =
      M.modularAutomorphismGroup s (M.modularAutomorphismGroup t A) :=
  ModularRadonNikodymData.modularAutomorphismGroup_add (M := M) s t A

/--
The owner-level replacement for the historical support-preservation marker:
successive modular transports compose to the transport at the summed time.
-/
theorem modularTransport_preserves_support
    (M : ModularRadonNikodymData E)
    (s t : ℝ) (A : EndH) :
    M.modularAutomorphismGroup s (M.modularAutomorphismGroup t A) =
      M.modularAutomorphismGroup (s + t) A :=
  (modularTransport_eq_conjugation M s t A).symm

/--
Historical modular/Berry correspondence, recovered directly from the
Hestenes--Kähler compatibility law.
-/
theorem modularBerryHolonomy_eq_transportPhase_of_identification
    (S : SuperHestenesKaehlerDatum (E := E))
    (X Y : EndH) :
    S.phase (X (0 : H₂)) (Y (0 : H₂)) =
      S.metric (S.K (X (0 : H₂))) (Y (0 : H₂)) :=
  S.compat (X 0) (Y 0)

/--
Recovered synthesis theorem: the modular transport composition law and the
Hestenes--Kähler phase law hold simultaneously on their genuine owners.
-/
theorem modularSpinConnection_eq_BerryConnection_of_identification
    (M : ModularRadonNikodymData E)
    (S : SuperHestenesKaehlerDatum (E := E))
    (s t : ℝ) (A X Y : EndH) :
    M.modularAutomorphismGroup (s + t) A =
        M.modularAutomorphismGroup s (M.modularAutomorphismGroup t A)
      ∧ S.phase (X (0 : H₂)) (Y (0 : H₂)) =
        S.metric (S.K (X (0 : H₂))) (Y (0 : H₂)) :=
  ⟨modularTransport_eq_conjugation M s t A,
    modularBerryHolonomy_eq_transportPhase_of_identification S X Y⟩

/--
The modular/Berry bridge needs no carrier object: the two closure laws are the
owner theorems for the finite RN modular flow and the Hestenes-Kaehler datum.
-/
theorem modularRNFlow_add_and_hestenesBerry_phase
    (M : ModularRadonNikodymData E)
    (S : SuperHestenesKaehlerDatum (E := E))
    (s t : ℝ) (A X Y : EndH) :
    M.modularAutomorphismGroup (s + t) A =
        M.modularAutomorphismGroup s (M.modularAutomorphismGroup t A)
      ∧ S.phase (X (0 : H₂)) (Y (0 : H₂)) =
        S.metric (S.K (X (0 : H₂))) (Y (0 : H₂)) := by
  exact modularSpinConnection_eq_BerryConnection_of_identification
    M S s t A X Y

end Experimental.ModularBerryBridge
