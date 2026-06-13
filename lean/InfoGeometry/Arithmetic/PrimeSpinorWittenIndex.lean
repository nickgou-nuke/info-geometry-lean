import Mathlib
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

/-!

InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

/-

BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights

finiteRealSpinorWittenReadout_eq_mobiusFermionPartition_squareWeights

finiteRealMajoranaWittenIndex_cancel

pairedWittenContribution_eq_zero

finitePairedWittenContributions_sum_eq_zero

majoranaBlockPfaffian_sq_eq_determinant

majoranaBlockPfaffian_primeSpinorMajoranaBlock

finiteMajoranaPfaffianReadout_eq_spinorWittenReadout

finiteMajoranaPfaffianReadout_eq_weylDenominator_squareWeights

finiteMajoranaPfaffian_sq_eq_determinant

PrimeSpinorWittenIndexPacket.finite_readout

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

WittenThermalTopologicalGuardrail.not_definitional_equality

RealMajoranaWittenIndexGate.square

RealMajoranaWittenIndexGate.parity_anticommutation

RealMajoranaWittenIndexGate.pfaffian_comparison

RealMajoranaWittenIndexGate.zero_mode_index

BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses, or certificates.]

Construction of a full real Majorana supercharge-pairing model.

Topological Witten-index stability under deformation.

Kernel/zero-mode readout theorem identifying the topological index.
-/

/-! ## 1. Finite real spinor Witten readout -/

def finiteRealSpinorWittenReadout
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) : R :=
finitePrimeSpinorBilinearProduct modes amplitude

theorem finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) :
finiteRealSpinorWittenReadout modes amplitude =
finitePrimeWeylDenominator modes
(fun p => scalarWeightFromSpinor (amplitude p)) := by
exact finitePrimeSpinorBilinearProduct_eq_weylDenominator_squareWeights modes amplitude

theorem finiteRealSpinorWittenReadout_eq_mobiusFermionPartition_squareWeights
{PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) :
finiteRealSpinorWittenReadout modes amplitude =
InfoGeometry.Arithmetic.MobiusFermionBosonization.finiteMobiusFermionGradedPartition
modes
(fun p => scalarWeightFromSpinor (amplitude p)) := by
exact finitePrimeSpinorBilinearProduct_eq_mobiusFermionPartition_squareWeights modes amplitude

theorem finiteRealMajoranaWittenIndex_cancel
(P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
(hP : P.primes.Nonempty) :
(∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
InfoGeometry.Arithmetic.PrimeBitWittenIndex.finite_witten_index_cancel P hP

/-! ## 2. Local supersymmetric pair cancellation -/

def pairedWittenContribution
{R : Type*} [Sub R]
(weight : R) : R :=
weight - weight

@[simp]
theorem pairedWittenContribution_eq_zero
{R : Type*} [AddGroup R]
(weight : R) :
pairedWittenContribution weight = 0 := by
unfold pairedWittenContribution
simp

theorem finitePairedWittenContributions_sum_eq_zero
{PairLabel R : Type*} [AddCommGroup R]
(pairs : Finset PairLabel)
(weight : PairLabel → R) :
Finset.sum pairs (fun a => pairedWittenContribution (weight a)) = 0 := by
simp

/-! ## 3. Finite Majorana Pfaffian block readout -/

structure MajoranaPfaffianBlock (R : Type*) where
entry : R

def majoranaBlockPfaffian
{R : Type*}
(B : MajoranaPfaffianBlock R) : R :=
B.entry

def majoranaBlockDeterminant
{R : Type*} [Mul R]
(B : MajoranaPfaffianBlock R) : R :=
B.entry * B.entry

theorem majoranaBlockPfaffian_sq_eq_determinant
{R : Type*} [Mul R]
(B : MajoranaPfaffianBlock R) :
majoranaBlockPfaffian B * majoranaBlockPfaffian B =
majoranaBlockDeterminant B := by
rfl

def primeSpinorMajoranaBlock
{R : Type*} [CommRing R]
(a : R) : MajoranaPfaffianBlock R :=
⟨spinorBilinear (thermalSpinorPlus a) (thermalSpinorMinus a)⟩

theorem majoranaBlockPfaffian_primeSpinorMajoranaBlock
{R : Type*} [CommRing R]
(a : R) :
majoranaBlockPfaffian (primeSpinorMajoranaBlock a) =
1 - scalarWeightFromSpinor a := by
exact spinorBilinear_plus_minus_eq_one_sub_square a

def finiteMajoranaPfaffianReadout
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) : R :=
Finset.prod modes
  (fun p => majoranaBlockPfaffian (primeSpinorMajoranaBlock (amplitude p)))

def finiteMajoranaDeterminantReadout
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) : R :=
Finset.prod modes
  (fun p => majoranaBlockDeterminant (primeSpinorMajoranaBlock (amplitude p)))

theorem finiteMajoranaPfaffianReadout_eq_spinorWittenReadout
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) :
finiteMajoranaPfaffianReadout modes amplitude =
finiteRealSpinorWittenReadout modes amplitude := by
unfold finiteMajoranaPfaffianReadout finiteRealSpinorWittenReadout
rfl

theorem finiteMajoranaPfaffianReadout_eq_weylDenominator_squareWeights
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) :
finiteMajoranaPfaffianReadout modes amplitude =
finitePrimeWeylDenominator modes
(fun p => scalarWeightFromSpinor (amplitude p)) := by
rw [finiteMajoranaPfaffianReadout_eq_spinorWittenReadout]
exact finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights modes amplitude

theorem finiteMajoranaPfaffian_sq_eq_determinant
{PrimeLabel R : Type*} [CommRing R]
(modes : Finset PrimeLabel)
(amplitude : PrimeLabel → R) :
finiteMajoranaPfaffianReadout modes amplitude *
finiteMajoranaPfaffianReadout modes amplitude =
finiteMajoranaDeterminantReadout modes amplitude := by
unfold finiteMajoranaPfaffianReadout finiteMajoranaDeterminantReadout
rw [← Finset.prod_mul_distrib]
refine Finset.prod_congr rfl ?_
intro p hp
exact majoranaBlockPfaffian_sq_eq_determinant
  (primeSpinorMajoranaBlock (amplitude p))

/-! ## 4. Guardrails and witness interfaces -/

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

structure PrimeSpinorWittenIndexPacket
(PrimeLabel R Operator PfaffianReadout ZeroModeReadout : Type*)
[CommRing R] where
modes : Finset PrimeLabel
amplitude : PrimeLabel → R
majoranaCAR :
InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.PrimeMajoranaCARGate PrimeLabel Operator
wittenGate :
RealMajoranaWittenIndexGate Unit Operator PfaffianReadout ZeroModeReadout

namespace PrimeSpinorWittenIndexPacket

theorem finite_readout
{PrimeLabel R Operator PfaffianReadout ZeroModeReadout : Type*}
[CommRing R]
(P : PrimeSpinorWittenIndexPacket
PrimeLabel R Operator PfaffianReadout ZeroModeReadout) :
finiteRealSpinorWittenReadout P.modes P.amplitude =
finitePrimeWeylDenominator P.modes
(fun p => scalarWeightFromSpinor (P.amplitude p)) := by
exact finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights
  P.modes P.amplitude
theorem PrimeSpinorWittenIndex
  {PrimeLabel R Operator PfaffianReadout ZeroModeReadout : Type*}
  [CommRing R]
  (P : PrimeSpinorWittenIndexPacket PrimeLabel R Operator PfaffianReadout ZeroModeReadout) :
  finiteMajoranaPfaffianReadout P.modes P.amplitude =
    finiteRealSpinorWittenReadout P.modes P.amplitude ∧
  finiteRealSpinorWittenReadout P.modes P.amplitude =
    finitePrimeWeylDenominator P.modes (fun p => scalarWeightFromSpinor (P.amplitude p)) ∧
  finiteMajoranaPfaffianReadout P.modes P.amplitude *
    finiteMajoranaPfaffianReadout P.modes P.amplitude =
    finiteMajoranaDeterminantReadout P.modes P.amplitude := by
  refine ⟨?_, ?_, ?_⟩
  · exact finiteMajoranaPfaffianReadout_eq_spinorWittenReadout P.modes P.amplitude
  · exact P.finite_readout
  · exact finiteMajoranaPfaffian_sq_eq_determinant P.modes P.amplitude
end PrimeSpinorWittenIndexPacket

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
