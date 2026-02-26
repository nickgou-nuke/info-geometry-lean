import InfoGeometry.Assumptions.LLN

/-!
# Experimental.AssumptionWrappers.LLN

Experimental wrapper over `InfoGeometry.Assumptions.LLN`.
This is the canonical migration home for legacy `Research.LLN` forwarding.
-/

namespace InfoGeometry.Experimental.AssumptionWrappers.LLN

export InfoGeometry.Assumptions.LLN (
  empiricalAverage
  fixed_partition_slln
  fixed_partition_slln_holds
  empirical_to_theoretical_slln
  ae_tendsto_ratio_to_rnDeriv
  ae_tendsto_ratio_to_rnDeriv_holds
)

end InfoGeometry.Experimental.AssumptionWrappers.LLN

