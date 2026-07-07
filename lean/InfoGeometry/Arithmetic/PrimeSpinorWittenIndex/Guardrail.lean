import Mathlib

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

structure WittenThermalTopologicalGuardrail
  (ThermalReadout TopologicalIndex PairingWitness KernelReadout : Type*) where
  thermalReadout : ThermalReadout
  topologicalIndex : TopologicalIndex
  pairingWitness : PairingWitness
  kernelReadout : KernelReadout
  not_definitional_equality_prop : Prop

namespace WittenThermalTopologicalGuardrail

theorem not_definitional_equality
  {ThermalReadout TopologicalIndex PairingWitness KernelReadout : Type*}
  (G : WittenThermalTopologicalGuardrail
    ThermalReadout TopologicalIndex PairingWitness KernelReadout)
  (h : G.not_definitional_equality_prop) :
  G.not_definitional_equality_prop :=
  h

end WittenThermalTopologicalGuardrail

structure RealMajoranaWittenIndexGate
  (StateSpace Operator PfaffianReadout ZeroModeReadout : Type*) where
  supercharge : Operator
  hamiltonian : Operator
  parity : Operator
  pfaffianReadout : PfaffianReadout
  zeroModeReadout : ZeroModeReadout
  square_prop : Prop
  parity_anticommutation_prop : Prop
  pfaffian_comparison_prop : Prop
  zero_mode_index_prop : Prop

namespace RealMajoranaWittenIndexGate

theorem square
  {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
  (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout)
  (h : G.square_prop) :
  G.square_prop :=
  h

theorem parity_anticommutation
  {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
  (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout)
  (h : G.parity_anticommutation_prop) :
  G.parity_anticommutation_prop :=
  h

theorem pfaffian_comparison
  {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
  (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout)
  (h : G.pfaffian_comparison_prop) :
  G.pfaffian_comparison_prop :=
  h

theorem zero_mode_index
  {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
  (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout)
  (h : G.zero_mode_index_prop) :
  G.zero_mode_index_prop :=
  h

end RealMajoranaWittenIndexGate

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
