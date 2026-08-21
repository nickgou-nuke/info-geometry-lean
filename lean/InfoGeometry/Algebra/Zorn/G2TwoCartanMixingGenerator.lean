import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity

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

theorem mixingBasis_admissible : admissibleBasis7 mixingBasis := by
  decide

noncomputable def cartanMixingAut : SplitOctF2Aut :=
  admissibleBasis7_to_aut mixingBasis mixingBasis_admissible

@[simp] theorem cartanMixingAut_on_basis7 (i : Fin 7) :
    cartanMixingAut.1 (basis7 i) = mixingBasis i := by
  fin_cases i <;> rfl

theorem cartanMixingAut_ne_one : cartanMixingAut ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) h
  simpa [cartanMixingAut, basis7, mixingBasis,
    admissibleBasis7_to_aut_apply, extendBasisMap, basis8From7,
    add, add2, one, ePlus, eMinus, up0, up1, up2, down0, down1,
    down2] using h0

end InfoGeometry.Algebra.Zorn.G2TwoCartanMixingGenerator
