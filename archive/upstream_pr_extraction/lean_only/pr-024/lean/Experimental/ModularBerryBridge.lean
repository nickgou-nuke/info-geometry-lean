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
  constructor
  · exact ModularRadonNikodymData.modularAutomorphismGroup_add (M := M) s t A
  · exact S.compat (X 0) (Y 0)

end Experimental.ModularBerryBridge
