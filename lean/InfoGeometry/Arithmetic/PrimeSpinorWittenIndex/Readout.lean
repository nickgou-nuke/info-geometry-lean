import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

noncomputable section

open scoped BigOperators

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

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

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
