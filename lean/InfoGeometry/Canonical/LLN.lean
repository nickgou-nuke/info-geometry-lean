import InfoGeometry.Assumptions.LLN

/-!
# InfoGeometry.Canonical.LLN

Canonical LLN surface built directly from `InfoGeometry.Assumptions.LLN`.
-/

namespace InfoGeometry.Canonical.LLN

/-!
Explicitly forward the LLN scaffold surface from the assumptions layer.
-/
export InfoGeometry.Assumptions.LLN (
  empiricalAverage
  fixed_partition_slln
  fixed_partition_slln_holds
  empirical_to_theoretical_slln
  ae_tendsto_ratio_to_rnDeriv
  ae_tendsto_ratio_to_rnDeriv_holds
)

end InfoGeometry.Canonical.LLN
