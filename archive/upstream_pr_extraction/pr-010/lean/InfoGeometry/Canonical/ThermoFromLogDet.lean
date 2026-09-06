import InfoGeometry.Thermo.FromLogDet

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
  partitionFromLogDet_def
  partitionFromLogDet_pos
  partitionFromLogDet_pos'
  gibbsProbFromLogDet_nonneg
  partitionFromLogDet_ne_zero
  gibbsProbFromLogDet_sum_one
  freeEnergyFromLogDet_eq_neg_scale_log_partition
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy_of_pos
)

@[simp] theorem energyFromLogDet_apply
    {n : ℕ} {Ω : Type _} [Fintype Ω]
    (X0 : InfoGeometry.Jordan.SPD n) (X : Ω → InfoGeometry.Jordan.SPD n) (ω : Ω) :
    energyFromLogDet X0 X ω = InfoGeometry.Jordan.logDetBregman (X ω) X0 := rfl

end InfoGeometry.Canonical.ThermoFromLogDet
