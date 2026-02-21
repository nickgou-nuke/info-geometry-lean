import InfoGeometry.Assumptions.LLN

/-!
# Research.LLN

Domain module for LLN/empirical-bridge draft APIs extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- explicit scaffold interface from `InfoGeometry.Assumptions.LLN`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.LLN

export InfoGeometry.Assumptions.LLN (
  fixed_partition_slln
  empirical_to_theoretical_slln
  ae_tendsto_ratio_to_rnDeriv
)

end InfoGeometry.Research.LLN

