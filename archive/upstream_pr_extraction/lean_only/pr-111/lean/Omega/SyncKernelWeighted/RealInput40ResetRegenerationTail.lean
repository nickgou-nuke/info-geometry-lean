import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper-facing wrapper for the real-input-40 reset-regeneration tail law.
    prop:real-input-40-reset-regeneration-tail -/
theorem paper_real_input_40_reset_regeneration_tail
    (survivalFormulaOnNonResetSector perronFrobeniusCertificate primitiveTransientSector
      tailFormula hasPerronRoot exponentialTailBound : Prop)
    (hasSurvivalFormulaOnNonResetSector : survivalFormulaOnNonResetSector)
    (hasPerronFrobeniusCertificate : perronFrobeniusCertificate)
    (hasPrimitiveTransientSector : primitiveTransientSector)
    (deriveTailFormula : survivalFormulaOnNonResetSector → tailFormula)
    (derivePerronRoot : perronFrobeniusCertificate → primitiveTransientSector → hasPerronRoot)
    (deriveExponentialTailBound : tailFormula → hasPerronRoot → exponentialTailBound) :
    tailFormula ∧ hasPerronRoot ∧ exponentialTailBound := by
  have hTail : tailFormula := deriveTailFormula hasSurvivalFormulaOnNonResetSector
  have hPerron : hasPerronRoot :=
    derivePerronRoot hasPerronFrobeniusCertificate hasPrimitiveTransientSector
  exact ⟨hTail, hPerron, deriveExponentialTailBound hTail hPerron⟩

end Omega.SyncKernelWeighted
