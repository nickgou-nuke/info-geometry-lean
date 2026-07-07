import Mathlib
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Readout
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Pfaffian
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Guardrail
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

noncomputable section

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

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
