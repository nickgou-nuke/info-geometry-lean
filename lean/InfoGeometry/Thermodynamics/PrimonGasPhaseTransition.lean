import Mathlib
import InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
/-!
# Primon gas partition readout

This module keeps a small theorem-honest interface between a finite primon-gas
packet and the analytic zeta readout.  It does **not** prove a Lee--Yang theorem,
a GUE spacing theorem, an AFRODITE-data comparison, or a crystallization theorem.
-/

namespace InfoGeometry.Thermodynamics

open Complex

/-- 
Finite symbolic readout for the zeta partition used by this phase-transition
socket.  The analytic zeta function is owned by the arithmetic/Bost-Connes
layers; this file only records the equality that a finite Primon-gas packet
must carry into that layer.
-/
noncomputable def zetaPartitionReadout (β : ℂ) : ℂ :=
  riemannZeta β

/-- The formal structure of a finite Primon-gas packet carrying a partition
readout at inverse temperature `β`. -/
structure PrimonGas where
  /-- The inverse temperature (Thermodynamic Time). -/
  β : ℂ
  /-- The finite partition readout carried by this phase-transition packet. -/
  partitionFunction : ℂ
  /-- The partition function must map to the zeta readout owned downstream. -/
  partition_eq_zeta : partitionFunction = zetaPartitionReadout β

/-- The Primon-gas packet exposes its carried partition/zeta equality. -/
theorem primon_partition_eq_zeta (gas : PrimonGas) :
    gas.partitionFunction = zetaPartitionReadout gas.β :=
  gas.partition_eq_zeta

/-- 
  The Burg Entropy / Free Energy of the Primon Gas.
  Φ = -(1/β) * ln(Ξ(β)).
  This thermodynamic potential generates the barrier function that 
  shapes the macroscopic volume of spacetime.
-/
def primonFreeEnergy (gas : PrimonGas) : ℂ :=
  -- This finite phase-transition layer keeps only the algebraic readout.
  -gas.partitionFunction

/-- Optional finite label packet for comparing with a random-matrix model.  This
is data only; no zeta-zero spacing theorem is asserted here. -/
structure RandomMatrixReadout where
  /-- The named spacing model. -/
  spacing_model : String

/-- A phase-transition point is a zero of the carried partition readout. -/
def IsPartitionZero (gas : PrimonGas) : Prop :=
  gas.partitionFunction = 0

/-- A packet carries the Wigner--Dyson label exactly when its model string is
`"Wigner-Dyson"`. -/
def HasWignerDysonReadout (packet : RandomMatrixReadout) : Prop :=
  packet.spacing_model = "Wigner-Dyson"

/-- The only theorem proved here: a zero of the carried partition function is a
zero of the declared zeta readout. -/
def phase_transition_zero_transfer : Prop :=
  ∀ gas : PrimonGas, IsPartitionZero gas → zetaPartitionReadout gas.β = 0

/-- Partition-zero transfer through the packet equality. -/
theorem phase_transition_zero_transfer_holds :
    phase_transition_zero_transfer := by
  intro gas hzero
  rw [← primon_partition_eq_zeta gas]
  exact hzero

/-- Statement shape for any later random-matrix comparison.  It is deliberately
not a theorem in this file. -/
def zeta_zero_random_matrix_spacing_statement : Prop :=
  ∀ gas : PrimonGas, IsPartitionZero gas → ∃ packet : RandomMatrixReadout, HasWignerDysonReadout packet

end InfoGeometry.Thermodynamics