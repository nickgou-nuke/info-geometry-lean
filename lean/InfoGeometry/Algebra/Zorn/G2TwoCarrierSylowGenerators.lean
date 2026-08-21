import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity

/-!
# Six carrier-level Sylow generators

The six coordinate packets below are the column images of the six matrices
checked by `scripts/verify_carrier_u64_exact.g`.  Each admissibility theorem is
checked on the finite Zorn carrier itself; no abstract group-order theorem is
imported.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoCarrierSylowGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def carrierBasis : Fin 6 → Fin 7 → SplitOctF2
  | 0 => ![
      ⟨false, true, false, false, false, false, false, true⟩,
      ⟨false, false, false, false, false, false, false, true⟩,
      ⟨false, false, false, false, false, false, true, true⟩,
      ⟨false, false, false, true, false, true, false, false⟩,
      ⟨true, true, false, true, false, false, false, true⟩,
      ⟨false, false, false, true, false, false, false, false⟩,
      ⟨false, false, true, false, false, false, false, false⟩]
  | 1 => ![
      ⟨true, false, false, false, false, false, false, false⟩,
      ⟨false, false, true, false, false, false, false, false⟩,
      ⟨false, false, false, true, false, false, false, false⟩,
      ⟨false, false, false, true, true, false, false, false⟩,
      ⟨false, false, false, false, false, true, false, false⟩,
      ⟨false, false, false, false, false, false, true, true⟩,
      ⟨false, false, false, false, false, false, false, true⟩]
  | 2 => ![
      ⟨true, false, false, false, false, false, false, true⟩,
      ⟨false, false, true, false, false, false, false, false⟩,
      ⟨false, false, false, true, false, false, false, false⟩,
      ⟨true, true, false, true, false, false, false, true⟩,
      ⟨false, false, false, true, true, false, false, false⟩,
      ⟨false, false, true, false, false, false, true, true⟩,
      ⟨false, false, false, false, false, false, false, true⟩]
  | 3 => ![
      ⟨true, false, false, false, false, false, false, true⟩,
      ⟨false, false, true, false, false, false, false, false⟩,
      ⟨false, false, true, true, false, false, false, false⟩,
      ⟨true, true, false, false, true, false, false, true⟩,
      ⟨true, true, false, true, false, true, true, true⟩,
      ⟨false, false, true, false, false, true, true, false⟩,
      ⟨false, false, false, false, false, false, false, true⟩]
  | 4 => ![
      ⟨true, false, false, false, false, false, false, true⟩,
      ⟨false, false, true, false, false, false, false, false⟩,
      ⟨false, false, false, true, true, false, false, false⟩,
      ⟨true, true, false, false, true, false, false, true⟩,
      ⟨false, false, false, true, true, true, false, false⟩,
      ⟨false, false, true, false, false, false, true, false⟩,
      ⟨false, false, false, false, false, false, false, true⟩]
  | 5 => ![
      ⟨true, false, false, false, false, false, false, false⟩,
      ⟨false, false, true, false, false, false, false, false⟩,
      ⟨false, false, false, true, false, false, false, false⟩,
      ⟨false, false, true, false, true, false, false, false⟩,
      ⟨false, false, false, false, false, true, false, true⟩,
      ⟨false, false, false, false, false, false, true, false⟩,
      ⟨false, false, false, false, false, false, false, true⟩]

theorem carrierBasis_admissible (i : Fin 6) :
    admissibleBasis7 (carrierBasis i) := by
  fin_cases i <;>
    unfold admissibleBasis7 <;>
    native_decide

noncomputable def carrierSylowGenerator (i : Fin 6) : SplitOctF2Aut :=
  admissibleBasis7_to_aut (carrierBasis i) (carrierBasis_admissible i)

@[simp] theorem carrierSylowGenerator_on_basis7 (i : Fin 6) (j : Fin 7) :
    (carrierSylowGenerator i).1 (basis7 j) = carrierBasis i j := by
  fin_cases j <;>
    simp [carrierSylowGenerator, admissibleBasis7_to_aut_apply,
      basis7, basis8From7, extendBasisMap, add, add2, zero,
      ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem carrierSylowGenerator_ne_one (i : Fin 6) :
    carrierSylowGenerator i ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis7 0)) h
  rw [carrierSylowGenerator_on_basis7] at h0
  fin_cases i <;>
    simp [carrierBasis, basis7, ePlus] at h0

end InfoGeometry.Algebra.Zorn.G2TwoCarrierSylowGenerators
