import InfoGeometry.Thermo.FromLogDet
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.ThermoFromLogDet

Canonical facade for thermodynamic constructions induced by log-det/Burg energy.
-/

namespace InfoGeometry.Canonical.ThermoFromLogDet

export InfoGeometry.Thermo (
  energyFromLogDet
  gibbsProbFromLogDet
  freeEnergyFromLogDet
  partitionFromLogDet
  partitionFromLogDet_pos
  partitionFromLogDet_pos'
  gibbsProbFromLogDet_nonneg
  partitionFromLogDet_ne_zero
  gibbsProbFromLogDet_sum_one
  freeEnergyFromLogDet_eq_neg_scale_log_partition
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy_of_pos
)

end InfoGeometry.Canonical.ThermoFromLogDet
