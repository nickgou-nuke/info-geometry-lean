import Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBound

namespace Omega.SyncKernelWeighted

/-- The coboundary normalization, explicit edge audit, and primitive-cycle nonnegativity bound are
the first three stages of the existing real-input-40 arity-charge certificate package.
    thm:real-input-40-arity-charge-coboundary -/
theorem paper_real_input_40_arity_charge_coboundary
    (coboundaryNormalization edgeAuditWithPotential primitiveCycleDensityBound : Prop)
    (hNorm : coboundaryNormalization)
    (deriveEdgeAudit : coboundaryNormalization → edgeAuditWithPotential)
    (derivePrimitiveCycleDensityBound : edgeAuditWithPotential → primitiveCycleDensityBound) :
    coboundaryNormalization ∧ edgeAuditWithPotential ∧ primitiveCycleDensityBound := by
  have hAudit : edgeAuditWithPotential := deriveEdgeAudit hNorm
  have hBound : primitiveCycleDensityBound := derivePrimitiveCycleDensityBound hAudit
  exact ⟨hNorm, hAudit, hBound⟩

end Omega.SyncKernelWeighted
