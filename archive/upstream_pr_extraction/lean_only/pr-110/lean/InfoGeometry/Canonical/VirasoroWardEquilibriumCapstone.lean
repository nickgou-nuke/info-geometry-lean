import InfoGeometry.Canonical.VirasoroWardEquilibrium
import InfoGeometry.Canonical.PrimeVirasoroSugawara

namespace InfoGeometry.Canonical.VirasoroWardEquilibriumCapstone

open InfoGeometry.Canonical.VirasoroWardEquilibrium
open InfoGeometry.Canonical.PrimeVirasoroSugawara

variable {Alg Op : Type*}
variable [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
variable [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]

/-- Capstone 3: Verification of Virasoro Ward equilibrium on the global log-potential. -/
theorem virasoro_ward_equilibrium_canonical_capstone
    (W : VirasoroWardEquilibriumPacket Alg Op)
    (n : ℤ) (hn : n ≥ -1) :
    W.wardResidual n = 0 ∧
    W.wardAction n (- Real.log W.thermodynamics.partitionFunction) = 0 := by
  constructor
  · exact W.wardResidual_eq_zero_of_globalMode n hn
  · exact W.wardAction_eq_zero_of_globalMode_negLogPartition n hn

end InfoGeometry.Canonical.VirasoroWardEquilibriumCapstone
