import Mathlib
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

/-!
# InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

Finite real/Majorana spinor Witten-index layer.

This file connects three finite theorem-bearing surfaces:

* the prime-bit Witten/Möbius parity layer;
* the real Majorana bit-flip layer;
* the spinor square-root bilinear layer.

The finite thermal graded readout is the Euler/Weyl denominator.  A genuinely
topological, parameter-independent Witten index requires a separate
supercharge-pairing model; this file exposes that as a witness interface rather
than silently identifying it with the thermal Euler product.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

/-! ## 1. Finite real spinor Witten readout -/

/--
Finite real spinor Witten readout.

For `amplitude p = p^{-s/2}`, this is the finite product of one-prime spinor
bilinears and represents the finite cutoff of the graded thermal readout.
-/
def finiteRealSpinorWittenReadout
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) : R :=
  finitePrimeSpinorBilinearProduct modes amplitude

/--
The finite real spinor Witten readout is the finite Euler/Weyl denominator with
squared spinor weights.
-/
theorem finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) :
    finiteRealSpinorWittenReadout modes amplitude =
      finitePrimeWeylDenominator modes
        (fun p => scalarWeightFromSpinor (amplitude p)) := by
  exact finitePrimeSpinorBilinearProduct_eq_weylDenominator_squareWeights modes amplitude

/--
The finite real spinor Witten readout equals the finite Möbius-fermion graded
partition with squared spinor weights.
-/
theorem finiteRealSpinorWittenReadout_eq_mobiusFermionPartition_squareWeights
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) :
    finiteRealSpinorWittenReadout modes amplitude =
      InfoGeometry.Arithmetic.MobiusFermionBosonization.finiteMobiusFermionGradedPartition
        modes
        (fun p => scalarWeightFromSpinor (amplitude p)) := by
  exact finitePrimeSpinorBilinearProduct_eq_mobiusFermionPartition_squareWeights modes amplitude

/--
Unweighted finite Witten cancellation for a nonempty real/Majorana prime
register.

This is inherited from the existing prime-bit theorem owner.
-/
theorem finiteRealMajoranaWittenIndex_cancel
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  InfoGeometry.Arithmetic.PrimeBitWittenIndex.finite_witten_index_cancel P hP

/-! ## 2. Local supersymmetric pair cancellation -/

/--
Signed contribution of one positive-energy SUSY pair.

Both partners carry the same thermal weight; their fermion parities are
opposite.
-/
def pairedWittenContribution
    {R : Type*} [Sub R]
    (weight : R) : R :=
  weight - weight

/-- A positive-energy paired contribution cancels in the Witten trace. -/
@[simp]
theorem pairedWittenContribution_eq_zero
    {R : Type*} [AddGroup R]
    (weight : R) :
    pairedWittenContribution weight = 0 := by
  unfold pairedWittenContribution
  simp

/--
Finite sum of paired positive-energy contributions cancels.

This is the finite algebraic content behind the usual Witten-index statement
that paired nonzero-energy states do not contribute.
-/
theorem finitePairedWittenContributions_sum_eq_zero
    {PairLabel R : Type*} [AddCommGroup R]
    (pairs : Finset PairLabel)
    (weight : PairLabel → R) :
    (∑ a ∈ pairs, pairedWittenContribution (weight a)) = 0 := by
  simp

/-! ## 3. Finite Majorana Pfaffian block readout -/

/--
One real Majorana `2 × 2` antisymmetric block, represented by its upper-right
entry.

It stands for the block `[[0, entry], [-entry, 0]]`.
-/
structure MajoranaPfaffianBlock (R : Type*) where
  entry : R

/-- Pfaffian of one represented `2 × 2` antisymmetric Majorana block. -/
def majoranaBlockPfaffian
    {R : Type*}
    (B : MajoranaPfaffianBlock R) : R :=
  B.entry

/-- Determinant readout of one represented `2 × 2` antisymmetric Majorana block. -/
def majoranaBlockDeterminant
    {R : Type*} [Mul R]
    (B : MajoranaPfaffianBlock R) : R :=
  B.entry * B.entry

/-- The represented `2 × 2` Majorana block satisfies `Pf² = det`. -/
theorem majoranaBlockPfaffian_sq_eq_determinant
    {R : Type*} [Mul R]
    (B : MajoranaPfaffianBlock R) :
    majoranaBlockPfaffian B * majoranaBlockPfaffian B =
      majoranaBlockDeterminant B := by
  rfl

/--
One-prime Majorana Pfaffian block from a spinor amplitude.

Its entry is the Euler factor `1 - a²`.
-/
def primeSpinorMajoranaBlock
    {R : Type*} [CommRing R]
    (a : R) : MajoranaPfaffianBlock R :=
  ⟨spinorBilinear (thermalSpinorPlus a) (thermalSpinorMinus a)⟩

/-- The Pfaffian of the one-prime spinor Majorana block is the Euler factor. -/
theorem majoranaBlockPfaffian_primeSpinorMajoranaBlock
    {R : Type*} [CommRing R]
    (a : R) :
    majoranaBlockPfaffian (primeSpinorMajoranaBlock a) =
      1 - scalarWeightFromSpinor a := by
  exact spinorBilinear_plus_minus_eq_one_sub_square a

/-- Finite direct-sum Pfaffian readout as the product of block Pfaffians. -/
def finiteMajoranaPfaffianReadout
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) : R :=
  ∏ p ∈ modes, majoranaBlockPfaffian (primeSpinorMajoranaBlock (amplitude p))

/-- Finite direct-sum determinant readout as the product of block determinants. -/
def finiteMajoranaDeterminantReadout
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) : R :=
  ∏ p ∈ modes, majoranaBlockDeterminant (primeSpinorMajoranaBlock (amplitude p))

/--
Finite Majorana Pfaffian readout equals the finite spinor Witten/Euler readout.
-/
theorem finiteMajoranaPfaffianReadout_eq_spinorWittenReadout
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) :
    finiteMajoranaPfaffianReadout modes amplitude =
      finiteRealSpinorWittenReadout modes amplitude := by
  unfold finiteMajoranaPfaffianReadout finiteRealSpinorWittenReadout
  rfl

/-- Finite Majorana Pfaffian readout equals the Euler/Weyl denominator. -/
theorem finiteMajoranaPfaffianReadout_eq_weylDenominator_squareWeights
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (amplitude : PrimeLabel → R) :
    finiteMajoranaPfaffianReadout modes amplitude =
      finitePrimeWeylDenominator modes
        (fun p => scalarWeightFromSpinor (amplitude p)) := by
  rw [finiteMajoranaPfaffianReadout_eq_spinorWittenReadout]
  exact finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights modes amplitude

/-- The finite direct-sum readouts satisfy `Pf² = det`. -/
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
  intro p _hp
  exact majoranaBlockPfaffian_sq_eq_determinant
    (primeSpinorMajoranaBlock (amplitude p))

/-! ## 4. Guardrails and witness interfaces -/

/--
Guardrail separating the thermal Euler readout from a parameter-independent
topological Witten index.

The finite Euler product is a graded thermal trace.  Interpreting it as a
topological Witten index requires extra data proving supercharge pairing,
kernel readout, and stability under the relevant deformation.
-/
structure WittenThermalTopologicalGuardrail
    (ThermalReadout TopologicalIndex PairingWitness KernelReadout : Type*) where
  thermalReadout : ThermalReadout
  topologicalIndex : TopologicalIndex
  pairingWitness : PairingWitness
  kernelReadout : KernelReadout
  not_definitional_equality : Prop
  certificate : not_definitional_equality

/--
Witness gate for a real Majorana Witten-index model.

The finite readouts in this file are theorem-bearing.  The full operator model
for a real supercharge, a Majorana Clifford representation, a Pfaffian readout,
and a zero-mode interpretation is supplied by an owning construction through
this gate.
-/
structure RealMajoranaWittenIndexGate
    (StateSpace Operator PfaffianReadout ZeroModeReadout : Type*) where
  supercharge : Operator
  hamiltonian : Operator
  parity : Operator
  pfaffianReadout : PfaffianReadout
  zeroModeReadout : ZeroModeReadout
  square_True : Prop
  parity_anticommutation_True : Prop
  pfaffian_comparison_True : Prop
  zero_mode_index_True : Prop
  certificate :
    square_True ∧
      parity_anticommutation_True ∧
        pfaffian_comparison_True ∧
          zero_mode_index_True

namespace RealMajoranaWittenIndexGate

/-- Re-export of the supplied supercharge square law. -/
theorem square
    {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
    (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout) :
    G.square_True :=
  G.certificate.1

/-- Re-export of the supplied Pfaffian comparison law. -/
theorem pfaffian_comparison
    {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
    (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout) :
    G.pfaffian_comparison_True :=
  G.certificate.2.2.1

/-- Re-export of the supplied zero-mode index law. -/
theorem zero_mode_index
    {StateSpace Operator PfaffianReadout ZeroModeReadout : Type*}
    (G : RealMajoranaWittenIndexGate StateSpace Operator PfaffianReadout ZeroModeReadout) :
    G.zero_mode_index_True :=
  G.certificate.2.2.2

end RealMajoranaWittenIndexGate

/--
Combined finite packet for the real spinor Witten readout.
-/
structure PrimeSpinorWittenIndexPacket
    (PrimeLabel R Operator PfaffianReadout ZeroModeReadout : Type*)
    [DecidableEq PrimeLabel] [CommRing R] where
  modes : Finset PrimeLabel
  amplitude : PrimeLabel → R
  majoranaCAR :
    InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.PrimeMajoranaCARGate PrimeLabel Operator
  wittenGate :
    RealMajoranaWittenIndexGate Unit Operator PfaffianReadout ZeroModeReadout
  finite_readout_True :
    finiteRealSpinorWittenReadout modes amplitude =
      finitePrimeWeylDenominator modes
        (fun p => scalarWeightFromSpinor (amplitude p))

namespace PrimeSpinorWittenIndexPacket

/-- Packet-level finite Euler/Witten readout theorem. -/
theorem finite_readout
    {PrimeLabel R Operator PfaffianReadout ZeroModeReadout : Type*}
    [DecidableEq PrimeLabel] [CommRing R]
    (P : PrimeSpinorWittenIndexPacket
      PrimeLabel R Operator PfaffianReadout ZeroModeReadout) :
    finiteRealSpinorWittenReadout P.modes P.amplitude =
      finitePrimeWeylDenominator P.modes
        (fun p => scalarWeightFromSpinor (P.amplitude p)) :=
  P.finite_readout_True

end PrimeSpinorWittenIndexPacket

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
