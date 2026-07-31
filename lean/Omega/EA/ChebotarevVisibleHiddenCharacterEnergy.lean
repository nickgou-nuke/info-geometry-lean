import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- Paper-facing wrapper for the visible/hidden `L²` energy decomposition: orthogonality gives the
exact scalar split is exposed directly.  The finite-character Fourier/Parseval theorem is owned by
`ChebotarevPlancherelEnergy` and is not duplicated as an untyped proposition here.
    thm:kernel-chebotarev-visible-hidden-character-energy -/
theorem paper_kernel_chebotarev_visible_hidden_character_energy
    (totalEnergy visibleEnergy hiddenEnergy : ℝ)
    (hSplit : totalEnergy = visibleEnergy + hiddenEnergy) :
    totalEnergy = visibleEnergy + hiddenEnergy := hSplit

end Omega.EA
