import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.LogDet
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.LogSumExp
import InfoGeometry.Canonical.ThermoFromLogDet
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.RedLine

Canonical bridge surface for the "Red Line":
log-volume deformation -> convex/barrier potential -> Burg/Bregman energy ->
partition/log-sum-exp -> free energy, with RN/Jaynes and modular lifts.
-/

namespace InfoGeometry.Canonical.RedLine

open InfoGeometry.Canonical.MoE

export InfoGeometry.Canonical.LogDet (
  logDetBarrier
  logDetBregman
  logDetBarrier_eq_neg_log_det
)

export InfoGeometry.Canonical.ThermoFromLogDet (
  energyFromLogDet
  partitionFromLogDet
  freeEnergyFromLogDet
  freeEnergyFromLogDet_eq_neg_scale_log_partition
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy
)

export InfoGeometry.Canonical.LogSumExp (
  logSumExpPartition
  logSumExp
  logSumExpScaledPartition
  logSumExpScaled
  logSumExp_eq_log_partition
)

export InfoGeometry.Canonical.JaynesRNMaxEnt (
  MomentFamily
  objectiveKL
  potential
  partitionFunction
  gibbsMeasure
  rnDeriv_gibbsMeasure_eq
  rnDeriv_gibbsMeasure_toReal_eq
  GibbsMinimizesKL
)

export InfoGeometry.Canonical.MoE (
  kahlerPotentialRN
  kahlerPotentialRN_eq_neg_logJacobian
  relativeVolumeChangeRN
  relativeVolumeChangeRN_eq_exp_logJacobian
  kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN
)

export InfoGeometry.Canonical.KMSSinkhornBridge (
  ibRNPotential_eq_scalarModularPotential_relativeVolumeChange
  jacobianRelativeVolume
  jacobianLogPotential
  exp_neg_jacobianLogPotential_eq_jacobianRelativeVolume
  jacobianLogPotential_eq_scalarModularPotential
)

export InfoGeometry.Canonical.RicciMongeAmpere (
  metricLogDet
  mongeAmpereDensity
  mongeAmpereDensity_eq_exp_metricLogDet
  metricLogDet_eq_log_mongeAmpereDensity
  scalarModularPotential_mongeAmpereDensity_eq_neg_metricLogDet
)

export InfoGeometry.Canonical.PositiveRayCore (
  PositiveRay
  PositiveOrthantRaySpace
  toConeInteriorStateSpace
  ofConeInteriorStateSpace
  gaugeSection
  Z_gaugeSection
  logDensity
  modularPotential
  gaugeSection_eq_exp_logDensity
  gaugeSection_eq_exp_neg_modularPotential
)

export InfoGeometry.Canonical.RelativePotentialCore (
  representativeRelativeDensity
  representativeRelativeLogDensity
  representativeModularPotential
  representativeRelativeLogDensity_eq_log_sub_log
  representativeRelativeDensity_eq_exp_representativeRelativeLogDensity
  representativeModularPotential_eq_neg_representativeRelativeLogDensity
  representativeRelativeLogDensity_scale_left
  representativeRelativeLogDensity_scale_right
  representativeRelativeLogDensity_scale_scale
  representativeModularPotential_scale_left
  representativeModularPotential_scale_right
  relativeDensity
  relativeLogDensity
  relativeModularPotential
  relativeLogDensity_eq_logDensity_sub_logDensity
  relativeDensity_eq_exp_relativeLogDensity
  relativeModularPotential_eq_neg_relativeLogDensity
  relativeModularPotential_eq_logDensity_base_sub_logDensity
  gaugeSection_eq_relativeDensity_mul_gaugeSection
  relativeDensity_self
  relativeLogDensity_self
  relativeModularPotential_self
)

export InfoGeometry.Canonical.RelativePotentialScalarBridge (
  scalarPositiveMeasure
  scalarLogDensity
  scalarModularPotential
  representativeRelativeDensity_scalar
  representativeRelativeLogDensity_scalar
  representativeModularPotential_scalar
  scalarLogDensity_eq_log
  scalarModularPotential_eq_neg_log
  exp_neg_scalarModularPotential_eq
)

export InfoGeometry.Canonical.RelativePotentialDiscreteBridge (
  gaugeSectionFinProb
  toProjectiveState
  gaugeSectionFinProb_absolutelyContinuous
  projectiveLogGenerator_eq_relativeModularPotential_ae
  projectiveLogGenerator_eq_relativeModularPotential
)

export InfoGeometry.Canonical.RelativePotentialCountBridge (
  RelativeCounts
  relativeCountDensity
  relativeCountDensity_eq_rn_lift
  relativeCountLogDensity
  relativeLogDensityMean
  relativeModularHamiltonian
  relativeTomitaTakesakiOp
  relativeTomitaTakesakiOp_apply
  positiveMeasureOfCounts
  countMass
  countRay
  gaugeSection_countRay_apply
  relativeDensity_countRay_eq_massRatio_mul_relativeCountDensity
  relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift
  relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_add_massShift
  projectiveLogGenerator_countRay_eq_neg_relativeCountLogDensity_add_massShift
)

export InfoGeometry.Canonical.TomitaTakesaki (
  DiagonalPositiveTimeVector
  PositiveTimeVector
  modularConjugationJ
  modularSignEpsilon
  modularComplexI
  modularSignAdditiveModularFlow
  modularAtomRepresentation
  tomitaRepresentation
)

@[simp] theorem redline_energy_is_burg
    {n : ℕ} {Ω : Type _} [Fintype Ω]
    (X0 : InfoGeometry.Jordan.SPD n) (X : Ω → InfoGeometry.Jordan.SPD n) (ω : Ω) :
    energyFromLogDet X0 X ω = logDetBregman (X ω) X0 := rfl

@[simp] theorem redline_freeEnergy_is_neg_log_partition
    {n : ℕ} {Ω : Type _} [Fintype Ω] [Nonempty Ω]
    (X0 : InfoGeometry.Jordan.SPD n) (X : Ω → InfoGeometry.Jordan.SPD n) (ε : ℝ) :
    freeEnergyFromLogDet X0 X ε = -ε * Real.log (partitionFromLogDet X0 X ε) := by
  exact freeEnergyFromLogDet_eq_neg_scale_log_partition (X0 := X0) (X := X) ε

end InfoGeometry.Canonical.RedLine
