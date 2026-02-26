import InfoGeometry.Experimental.AssumptionWrappers.LLN

/-!
# Research.LLN

Compatibility forwarder over `InfoGeometry.Experimental.AssumptionWrappers.LLN`.
-/

namespace InfoGeometry.Canonical.LLN

/-!
Explicitly forward the LLN scaffold surface from the experimental wrapper.
-/
export InfoGeometry.Experimental.AssumptionWrappers.LLN (
  empiricalAverage
  fixed_partition_slln
  fixed_partition_slln_holds
  empirical_to_theoretical_slln
  ae_tendsto_ratio_to_rnDeriv
  ae_tendsto_ratio_to_rnDeriv_holds
)

end InfoGeometry.Canonical.LLN
