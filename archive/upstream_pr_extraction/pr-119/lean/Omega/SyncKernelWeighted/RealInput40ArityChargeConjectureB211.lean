import Omega.SyncKernelWeighted.RealInput40ArityChargeCoboundary

namespace Omega.SyncKernelWeighted

/-- Standalone corollary extracting the primitive-cycle nonnegativity consequence recorded in the
real-input-40 arity-charge coboundary certificate.
    cor:real-input-40-arity-charge-conjecture-b211 -/
theorem paper_real_input_40_arity_charge_conjecture_b211
    (coboundaryNormalization edgeAuditWithPotential primitiveCycleDensityBound : Prop)
    (hNorm : coboundaryNormalization)
    (deriveEdgeAudit : coboundaryNormalization → edgeAuditWithPotential)
    (derivePrimitiveCycleDensityBound : edgeAuditWithPotential → primitiveCycleDensityBound) :
    primitiveCycleDensityBound := by
  exact (paper_real_input_40_arity_charge_coboundary coboundaryNormalization
    edgeAuditWithPotential primitiveCycleDensityBound hNorm deriveEdgeAudit
    derivePrimitiveCycleDensityBound).2.2

end Omega.SyncKernelWeighted
