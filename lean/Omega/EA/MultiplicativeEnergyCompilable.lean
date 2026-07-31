import Mathlib.Tactic

namespace Omega.EA

/-- Paper-facing wrapper for the multiplicative-energy compilability package: once the four-track
product transducer has been compiled to a finite transition matrix, the path-count identity yields
the matrix-power formula `E_x(A_m) = uᵀ B_x^m v`, and the Perron-Frobenius growth package gives the
claimed exponential rate.
    prop:conclusion71-multiplicative-energy-compilable -/
theorem paper_conclusion71_multiplicative_energy_compilable
    (fourTrackProductBuilt finiteTransitionMatrixExtracted pathCountIdentity
      perronFrobeniusPackage matrixPowerFormula exponentialGrowthRate : Prop)
    (fourTrackProductBuilt_h : fourTrackProductBuilt)
    (finiteTransitionMatrixExtracted_h : finiteTransitionMatrixExtracted)
    (derivePathCountIdentity :
      fourTrackProductBuilt → finiteTransitionMatrixExtracted → pathCountIdentity)
    (deriveMatrixPowerFormula : pathCountIdentity → matrixPowerFormula)
    (derivePerronFrobeniusPackage : matrixPowerFormula → perronFrobeniusPackage)
    (deriveExponentialGrowthRate : perronFrobeniusPackage → exponentialGrowthRate) :
    matrixPowerFormula ∧ exponentialGrowthRate := by
  have hPath : pathCountIdentity :=
    derivePathCountIdentity fourTrackProductBuilt_h finiteTransitionMatrixExtracted_h
  have hMatrix : matrixPowerFormula := deriveMatrixPowerFormula hPath
  have hPF : perronFrobeniusPackage := derivePerronFrobeniusPackage hMatrix
  exact ⟨hMatrix, deriveExponentialGrowthRate hPF⟩

end Omega.EA
