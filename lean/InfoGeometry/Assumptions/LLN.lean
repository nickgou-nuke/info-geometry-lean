import InfoGeometry.Canonical.LLN

/-!
# Assumptions.LLN

DEPRECATED compatibility shim.

New code should import:
- `InfoGeometry.Canonical.LLN`

Compatibility re-export of the canonical LLN core.
This keeps legacy `InfoGeometry.Assumptions.LLN.*` paths stable while removing
duplicated definitions.
-/

namespace InfoGeometry.Assumptions.LLN

export InfoGeometry.Canonical.LLN
  (empiricalAverage
   fixed_partition_slln
   fixed_partition_slln_holds
   empirical_to_theoretical_slln
   ae_tendsto_ratio_to_rnDeriv
   ae_tendsto_ratio_to_rnDeriv_holds)

end InfoGeometry.Assumptions.LLN
