import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Readout
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Pfaffian

noncomputable section

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

structure PrimeSpinorWittenIndexPacket
  (PrimeLabel R : Type*)
  [CommRing R] where
  modes : Finset PrimeLabel
  amplitude : PrimeLabel → R

namespace PrimeSpinorWittenIndexPacket

theorem finite_readout
  {PrimeLabel R : Type*}
  [CommRing R]
  (P : PrimeSpinorWittenIndexPacket PrimeLabel R) :
  finiteRealSpinorWittenReadout P.modes P.amplitude =
  finitePrimeWeylDenominator P.modes
    (fun p => scalarWeightFromSpinor (P.amplitude p)) := by
  exact finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights
    P.modes P.amplitude

theorem PrimeSpinorWittenIndex
  {PrimeLabel R : Type*}
  [CommRing R]
  (P : PrimeSpinorWittenIndexPacket PrimeLabel R) :
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
