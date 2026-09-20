import InfoGeometry.Millennium.YangMillsMassGapAudit

namespace InfoGeometry.Millennium.YangMillsMassGapAuditTests

open InfoGeometry.Millennium.YangMillsMassGapAudit

example : ∀ state : PositiveEnergyState, 0 < totalSquared state := totalSquared_pos

example : ¬ ∃ gap : ℝ, 0 < gap ∧ ∀ state : PositiveEnergyState, gap ≤ totalSquared state :=
  no_uniform_positive_lower_bound

example : ∃ state : PositiveEnergyState, 0 < totalSquared state ∧ totalSquared state < 1 / 1000 :=
  arbitrarily_small_positive_energy _ (by norm_num)

#print axioms InfoGeometry.Millennium.YangMillsMassGapAudit.no_uniform_positive_lower_bound

end InfoGeometry.Millennium.YangMillsMassGapAuditTests
