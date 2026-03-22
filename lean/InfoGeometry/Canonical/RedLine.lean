import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.LogDet
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
)

export InfoGeometry.Canonical.GrandSynthesis (
  relativeModularHamiltonian
  relativeTomitaTakesakiOp
  relativeTomitaTakesakiOp_apply
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
