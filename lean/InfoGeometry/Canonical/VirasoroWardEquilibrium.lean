import InfoGeometry.Canonical.OperatorThermodynamics
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.Meta.Architecture

noncomputable section

/-!
# InfoGeometry.Canonical.VirasoroWardEquilibrium

Theorem-safe bridge for the Virasoro Ward/equilibrium reading of a global
log-partition potential.

This file does not assert a new GW or Virasoro ontology.  It only packages the
existing operator thermodynamics packet together with an abstract Virasoro datum
and a residual-zero Ward constraint:

* the thermodynamic side owns `freeEnergy = -log partitionFunction`;
* the Virasoro side owns the symmetry datum;
* the Ward constraint is a residual equation on the free-energy readout;
* the global modes are the modes for which that residual vanishes.

The role of the file is to make the "Virasoro constraints as equilibrium
equations" interpretation explicit without turning it into an ax!om.
-/

namespace InfoGeometry.Canonical.VirasoroWardEquilibrium

open InfoGeometry.Canonical.OperatorThermodynamics
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/--
Virasoro Ward equilibrium packet.

`wardAction` is the abstract mode action on the scalar free-energy readout.
`wardConstraint` is the residual-zero predicate.  The file does not identify the
action with a concrete differential operator; that is left to later owner
instantiations.
-/
structure VirasoroWardEquilibriumPacket
    (Alg Op : Type*)
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op] where
  /-- Virasoro generator datum. -/
  virasoro : VirasoroDatum Alg

  /-- Thermodynamic owner packet carrying the global log-partition potential. -/
  thermodynamics : OperatorFirstThermodynamicsPacket Unit Op

  /-- Abstract Ward action on the scalar free-energy readout. -/
  wardAction : ℤ → ℝ → ℝ

  /-- Residual-zero Ward constraint. -/
  wardConstraint : ℤ → Prop

  /-- The Ward constraint is exactly vanishing of the residual action. -/
  wardConstraint_eq_zero :
    ∀ n : ℤ, wardConstraint n ↔ wardAction n thermodynamics.freeEnergy = 0

  /--
  Global Virasoro/Ward equilibrium on the nonnegative and `-1` modes.

  This is the abstract equilibrium packet: the concrete mode action is supplied
  by the caller.
  -/
  globalWardConstraint :
    ∀ n : ℤ, n ≥ -1 → wardConstraint n

namespace VirasoroWardEquilibriumPacket

variable {Alg Op : Type*}
variable [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
variable [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]

/-- The free-energy readout of a Virasoro Ward packet is the existing operatorial one. -/
@[simp]
theorem freeEnergy_eq_neg_log_partition
    (W : VirasoroWardEquilibriumPacket Alg Op) :
    W.thermodynamics.freeEnergy =
      - Real.log W.thermodynamics.partitionFunction :=
  rfl

/-- The Ward residual is the abstract action applied to the free-energy readout. -/
def wardResidual (W : VirasoroWardEquilibriumPacket Alg Op) (n : ℤ) : ℝ :=
  W.wardAction n W.thermodynamics.freeEnergy

@[simp]
theorem wardResidual_eq_wardAction_freeEnergy
    (W : VirasoroWardEquilibriumPacket Alg Op) (n : ℤ) :
    W.wardResidual n = W.wardAction n W.thermodynamics.freeEnergy :=
  rfl

/-- The Ward constraint is equivalent to vanishing Ward residual. -/
@[simp]
theorem wardConstraint_iff_wardResidual_eq_zero
    (W : VirasoroWardEquilibriumPacket Alg Op) (n : ℤ) :
    W.wardConstraint n ↔ W.wardResidual n = 0 := by
  simpa [wardResidual] using W.wardConstraint_eq_zero n

/-- Global Virasoro/Ward equilibrium kills the residual on admissible modes. -/
theorem wardResidual_eq_zero_of_globalMode
    (W : VirasoroWardEquilibriumPacket Alg Op) (n : ℤ) (hn : n ≥ -1) :
    W.wardResidual n = 0 := by
  exact (W.wardConstraint_iff_wardResidual_eq_zero n).mp
    (W.globalWardConstraint n hn)

/-- Global Virasoro/Ward equilibrium on the negative-log partition potential. -/
theorem wardAction_eq_zero_of_globalMode_negLogPartition
    (W : VirasoroWardEquilibriumPacket Alg Op) (n : ℤ) (hn : n ≥ -1) :
    W.wardAction n (- Real.log W.thermodynamics.partitionFunction) = 0 := by
  rw [← W.freeEnergy_eq_neg_log_partition]
  exact W.wardResidual_eq_zero_of_globalMode n hn

/-- The Virasoro Ward packet exposes the free energy as the global log-potential. -/
theorem thermodynamics_freeEnergy_eq_neg_log_partition
    (W : VirasoroWardEquilibriumPacket Alg Op) :
    W.thermodynamics.freeEnergy =
      - Real.log W.thermodynamics.partitionFunction :=
  W.freeEnergy_eq_neg_log_partition

/--
Canonical vacuum/trivial equilibrium packet where all Ward variations vanish identically.
-/
def ofTrivialEquilibrium
    (V : VirasoroDatum Alg)
    (T : OperatorFirstThermodynamicsPacket Unit Op) :
    VirasoroWardEquilibriumPacket Alg Op where
  virasoro := V
  thermodynamics := T
  wardAction := fun _ _ => 0
  wardConstraint := fun _ => True
  wardConstraint_eq_zero := fun _ => by simp
  globalWardConstraint := fun _ _ => trivial

end VirasoroWardEquilibriumPacket

end InfoGeometry.Canonical.VirasoroWardEquilibrium
