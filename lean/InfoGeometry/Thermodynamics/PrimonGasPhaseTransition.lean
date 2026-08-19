import Mathlib.Tactic
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
interface.  The analytic zeta function is owned by the arithmetic/Bost-Connes
layers; this file only records the equality that a finite Primon-gas packet
must carry into that layer.
-/
noncomputable def zetaPartitionReadout (β : ℂ) : ℂ :=
  riemannZeta β

/-- The formal structure of a finite Primon-gas packet carrying a partition
readout at inverse temperature `β`. -/
abbrev PrimonGas := ℂ

namespace PrimonGas

abbrev β (gas : PrimonGas) : ℂ := gas

noncomputable def partitionFunction (gas : PrimonGas) : ℂ :=
  zetaPartitionReadout gas.β

end PrimonGas

/-- The Primon-gas packet exposes its carried partition/zeta equality. -/
theorem primon_partition_eq_zeta (gas : PrimonGas) :
    gas.partitionFunction = zetaPartitionReadout gas.β :=
  rfl

theorem primon_partition_eq_riemannZeta (gas : PrimonGas) :
    gas.partitionFunction = riemannZeta gas.β := by
  rfl

/-- A scalar negation of the carried partition readout.
This definition is only an algebraic finite-model readout; no entropy,
variational, or phase-transition theorem is inferred from it. -/
noncomputable def primonFreeEnergy (gas : PrimonGas) : ℂ :=
  -- This finite phase-transition layer keeps only the algebraic readout.
  -gas.partitionFunction

/-- Optional finite label packet for comparing with a random-matrix model.  This
is data only; no zeta-zero spacing theorem is asserted here. -/
inductive RandomMatrixSpacingModel where
  | wignerDyson
  | other
  deriving DecidableEq, Repr

/-! The random-matrix readout is the typed spacing model itself. -/
abbrev RandomMatrixReadout := RandomMatrixSpacingModel

/-- A phase-transition point is a zero of the carried partition readout. -/
def IsPartitionZero (gas : PrimonGas) : Prop :=
  gas.partitionFunction = 0

/-- A packet carries the Wigner--Dyson label exactly when its typed model is
`RandomMatrixSpacingModel.wignerDyson`. -/
def HasWignerDysonReadout (packet : RandomMatrixReadout) : Prop :=
  packet = RandomMatrixSpacingModel.wignerDyson

/-- The only theorem proved here: a zero of the carried partition function is a
zero of the declared zeta readout. -/
theorem phase_transition_zero_transfer
    (gas : PrimonGas) (hzero : IsPartitionZero gas) :
    zetaPartitionReadout gas.β = 0 := by
  rw [← primon_partition_eq_zeta gas]
  exact hzero

/-- Partition-zero transfer through the packet equality. -/
theorem phase_transition_zero_transfer_holds :
    ∀ gas : PrimonGas, IsPartitionZero gas → zetaPartitionReadout gas.β = 0 := by
  intro gas hzero
  exact phase_transition_zero_transfer gas hzero

theorem phase_transition_zero_to_riemannZeta
    (gas : PrimonGas) (hzero : IsPartitionZero gas) :
    riemannZeta gas.β = 0 := by
  rw [← primon_partition_eq_riemannZeta gas]
  exact hzero

/-- Statement shape for any later random-matrix comparison.  It is deliberately
not a theorem in this file. -/
theorem wignerDysonReadout_exists :
    ∃ packet : RandomMatrixReadout, HasWignerDysonReadout packet := by
  exact ⟨RandomMatrixSpacingModel.wignerDyson, rfl⟩

theorem wignerDysonReadout_iff (packet : RandomMatrixReadout) :
    HasWignerDysonReadout packet ↔
      packet = RandomMatrixSpacingModel.wignerDyson := by
  rfl

end InfoGeometry.Thermodynamics
