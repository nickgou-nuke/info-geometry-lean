/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Tactic
import InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
/-!
# Primon Gas Partition Readout

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

/-- The finite algebraic free-energy readout of the Primon gas. -/
def primonFreeEnergy (gas : PrimonGas) : ℂ :=
  -gas.partitionFunction

/-- The Primon free-energy readout equals `-zetaPartitionReadout gas.β`. -/
theorem primonFreeEnergy_eq_neg_zeta (gas : PrimonGas) :
    primonFreeEnergy gas = -zetaPartitionReadout gas.β := by
  unfold primonFreeEnergy
  rw [primon_partition_eq_zeta gas]

/-- Optional finite label packet for comparing with a random-matrix model. -/
inductive RandomMatrixSpacingModel where
  | wignerDyson
  | other
  deriving DecidableEq, Repr

/-- The random-matrix readout is the typed spacing model itself. -/
abbrev RandomMatrixReadout := RandomMatrixSpacingModel

/-- Set of Primon-gas packets whose carried partition readout vanishes. -/
def partitionZeroSet : Set PrimonGas :=
  {gas : PrimonGas | gas.partitionFunction = 0}

/-- Set of random-matrix readouts carrying the Wigner–Dyson label. -/
def wignerDysonReadoutSet : Set RandomMatrixReadout :=
  {packet : RandomMatrixReadout | packet = RandomMatrixSpacingModel.wignerDyson}

/-- Partition-zero transfer through the packet equality: a zero of the carried
partition function is a zero of `zetaPartitionReadout gas.β`. -/
theorem phase_transition_zero_transfer_holds (gas : PrimonGas)
    (hzero : gas ∈ partitionZeroSet) :
    zetaPartitionReadout gas.β = 0 := by
  rw [← primon_partition_eq_zeta gas]
  exact hzero

end InfoGeometry.Thermodynamics
