import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2TwoCartanMixingGenerator

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def mixingBasis : Fin 7 → SplitOctF2 :=
  ![ ⟨true, false, true, false, false, false, true, false⟩,
     ⟨false, false, false, false, true, false, true, false⟩,
     ⟨false, false, true, false, false, false, false, false⟩,
     ⟨true, true, false, true, false, false, true, true⟩,
     ⟨false, false, true, false, false, false, false, true⟩,
     ⟨true, true, true, false, true, true, true, false⟩,
     ⟨false, false, false, false, false, false, true, false⟩ ]

noncomputable def cartanMixingAut
    (h : admissibleBasis7 mixingBasis) : SplitOctF2Aut :=
  admissibleBasis7_to_aut mixingBasis h

@[simp] theorem cartanMixingAut_on_basis7
    (h : admissibleBasis7 mixingBasis) (i : Fin 7) :
    (cartanMixingAut h).1 (basis7 i) = mixingBasis i := by
  fin_cases i <;> rfl

theorem cartanMixingAut_ne_one
    (h : admissibleBasis7 mixingBasis) :
    cartanMixingAut h ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) h
  change (cartanMixingAut _).1 (basis7 0) = (1 : SplitOctF2Aut).1 (basis7 0) at h0
  rw [cartanMixingAut_on_basis7] at h0
  have h1 : mixingBasis 0 ≠ basis7 0 := by
    decide
  exact h1 h0

theorem mixingBasis_zero_ne_ePlus : mixingBasis 0 ≠ ePlus := by
  decide

theorem mixingBasis_zero_ne_eMinus : mixingBasis 0 ≠ eMinus := by
  decide

end InfoGeometry.Algebra.Zorn.G2TwoCartanMixingGenerator
