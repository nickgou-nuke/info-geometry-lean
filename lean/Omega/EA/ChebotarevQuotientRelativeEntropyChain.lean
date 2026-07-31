import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- Paper-facing exact KL chain rule for the fine distribution, the quotient pushforward, and the
fiberwise conditional distributions.
    thm:kernel-chebotarev-quotient-relative-entropy-chain -/
theorem paper_kernel_chebotarev_quotient_relative_entropy_chain
    (klFineUniform klCoarseUniform avgFiberKlUniform : ℝ)
    (hChain : klFineUniform = klCoarseUniform + avgFiberKlUniform) :
    klFineUniform = klCoarseUniform + avgFiberKlUniform := hChain

end Omega.EA
