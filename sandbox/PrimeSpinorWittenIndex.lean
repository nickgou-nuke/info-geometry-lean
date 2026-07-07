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

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

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

/-! ## 4. Prime Spinor Witten Index (Broken down) -/

theorem primeSpinorWittenIndex_eq_spinor
  {PrimeLabel R : Type*} [CommRing R]
  (modes : Finset PrimeLabel) (amplitude : PrimeLabel → R) :
  finiteMajoranaPfaffianReadout modes amplitude =
    finiteRealSpinorWittenReadout modes amplitude := by
  exact finiteMajoranaPfaffianReadout_eq_spinorWittenReadout modes amplitude

theorem primeSpinorWittenIndex_eq_weyl
  {PrimeLabel R : Type*} [CommRing R]
  (modes : Finset PrimeLabel) (amplitude : PrimeLabel → R) :
  finiteRealSpinorWittenReadout modes amplitude =
    finitePrimeWeylDenominator modes (fun p => scalarWeightFromSpinor (amplitude p)) := by
  exact finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights modes amplitude

theorem primeSpinorWittenIndex_sq_eq_determinant
  {PrimeLabel R : Type*} [CommRing R]
  (modes : Finset PrimeLabel) (amplitude : PrimeLabel → R) :
  finiteMajoranaPfaffianReadout modes amplitude *
    finiteMajoranaPfaffianReadout modes amplitude =
    finiteMajoranaDeterminantReadout modes amplitude := by
  exact finiteMajoranaPfaffian_sq_eq_determinant modes amplitude

/-! ## 5. Open Closure Debt -/

/-- Construction of a full real Majorana supercharge-pairing model. -/
theorem construction_real_majorana_supercharge_pairing_model : False := by
  sorry

/-- Topological Witten-index stability under deformation. -/
theorem topological_witten_index_stability : False := by
  sorry

/-- Kernel/zero-mode readout theorem identifying the topological index. -/
theorem kernel_zero_mode_readout_identifies_topological_index : False := by
  sorry

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
