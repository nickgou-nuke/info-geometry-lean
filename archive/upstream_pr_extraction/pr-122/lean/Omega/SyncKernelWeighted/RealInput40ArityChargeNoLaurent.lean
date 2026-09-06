import Omega.SyncKernelWeighted.RealInput40Arity2dNonnegative

namespace Omega.SyncKernelWeighted

/-- File-local package for the no-Laurent conclusion: the coboundary audit certifies the primitive
support bound, and the 2D support wrapper records that every surviving monomial has nonnegative
`q`-exponent. -/
def real_input_40_arity_charge_no_laurent_statement
    (coboundaryNormalization edgeAuditWithPotential primitiveCycleDensityBound : Prop) : Prop :=
  coboundaryNormalization ∧
    edgeAuditWithPotential ∧
    primitiveCycleDensityBound ∧
    ∀ t ∈ real_input_40_arity_2d_nonnegative_terms primitiveCycleDensityBound, ¬ t.qExponent < 0

/-- Paper label: `cor:real-input-40-arity-charge-no-laurent`. -/
theorem paper_real_input_40_arity_charge_no_laurent
    (coboundaryNormalization edgeAuditWithPotential primitiveCycleDensityBound : Prop)
    (hNorm : coboundaryNormalization)
    (deriveEdgeAudit : coboundaryNormalization → edgeAuditWithPotential)
    (derivePrimitiveCycleDensityBound : edgeAuditWithPotential → primitiveCycleDensityBound) :
    real_input_40_arity_charge_no_laurent_statement coboundaryNormalization
      edgeAuditWithPotential primitiveCycleDensityBound := by
  have hCoboundary := paper_real_input_40_arity_charge_coboundary
    coboundaryNormalization edgeAuditWithPotential primitiveCycleDensityBound hNorm
    deriveEdgeAudit derivePrimitiveCycleDensityBound
  rcases paper_real_input_40_arity_2d_nonnegative primitiveCycleDensityBound hCoboundary.2.2 with
    ⟨_, hNoNeg⟩
  exact ⟨hCoboundary.1, hCoboundary.2.1, hCoboundary.2.2, hNoNeg⟩

end Omega.SyncKernelWeighted
