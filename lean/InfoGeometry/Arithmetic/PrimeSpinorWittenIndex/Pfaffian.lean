import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Readout
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

noncomputable section

open scoped BigOperators

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

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

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
