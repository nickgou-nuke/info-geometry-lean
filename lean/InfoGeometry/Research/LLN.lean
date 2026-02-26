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

@[deprecated InfoGeometry.Assumptions.LLN.fixed_partition_slln (since := "2026-02-25")]
abbrev fixed_partition_slln : Prop :=
  InfoGeometry.Assumptions.LLN.fixed_partition_slln

@[deprecated InfoGeometry.Assumptions.LLN.empirical_to_theoretical_slln (since := "2026-02-25")]
abbrev empirical_to_theoretical_slln : Prop :=
  InfoGeometry.Assumptions.LLN.empirical_to_theoretical_slln

@[deprecated InfoGeometry.Assumptions.LLN.ae_tendsto_ratio_to_rnDeriv (since := "2026-02-25")]
abbrev ae_tendsto_ratio_to_rnDeriv : Prop :=
  InfoGeometry.Assumptions.LLN.ae_tendsto_ratio_to_rnDeriv

end InfoGeometry.Research.LLN
