import InfoGeometry.Canonical.VirasoroWardEquilibrium
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.VirasoroWardEquilibriumCapstone

open InfoGeometry.Canonical.VirasoroWardEquilibrium

variable {Alg Op : Type*}
variable [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
variable [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/-- Global Ward equilibrium is the residual-zero statement on the existing
    thermodynamic free-energy readout. -/
theorem virasoro_ward_equilibrium_canonical_capstone
    (W : VirasoroWardEquilibriumPacket Alg Op) (n : ℤ) (hn : n ≥ -1) :
    W.wardResidual n = 0 ∧
    W.wardAction n (- Real.log W.thermodynamics.partitionFunction) = 0 := by
  exact ⟨W.wardResidual_eq_zero_of_globalMode n hn,
    W.wardAction_eq_zero_of_globalMode_negLogPartition n hn⟩

end InfoGeometry.Canonical.VirasoroWardEquilibriumCapstone
