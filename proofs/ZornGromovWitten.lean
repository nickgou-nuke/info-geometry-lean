import proofs.ZornChiralLightcone

/-!
# A complex structure from the chiral grading

This module defines `J = i · χ` from the canonical chirality involution and
proves its elementary operator identities.  The historical name is retained for
API compatibility.  No moduli space, pseudoholomorphic curve, or
Gromov--Witten invariant is constructed here.
-/

noncomputable section

namespace ZornGromovWitten

open CliffordAlgebra LinearMap
open ZornChiralLightcone CanonicalZornCompositionTriality
  CanonicalZornCliffordRepresentation

/-- The complex structure `i · χ` induced by the chiral grading. -/
def gromovJStructure : Module.End ℂ DiracSpinor16 :=
  Complex.I • chiralityOperator

/-- Scalar linearity of the negative chiral Clifford action, inherited from
the bundled linear map `diracGamma V`. -/
theorem cliffordMinus_smul (c : ℂ) (V : Vector8) (C : SpinorMinus8) :
    cliffordMinus V (c • C) = c • cliffordMinus V C := by
  have h := (diracGamma V).map_smul c (0, C)
  exact congrArg Prod.fst h

@[simp] theorem gromovJStructure_apply (S : SpinorPlus8) (C : SpinorMinus8) :
    gromovJStructure (S, C) = (Complex.I • S, -(Complex.I • C)) := by
  simp [gromovJStructure, chiralityOperator]

/-- The grading-derived complex structure squares to `-1`. -/
theorem gromovJStructure_sq :
    gromovJStructure * gromovJStructure = - 1 := by
  rw [gromovJStructure, smul_mul_smul, chiralityOperator_sq,
    Complex.I_mul_I]
  exact neg_one_smul ℂ (1 : Module.End ℂ DiracSpinor16)

/-- `J` acts by `i` on the positive chiral projector. -/
theorem gromovJStructure_peirce_plus :
    gromovJStructure * peirceProjectorPlus = Complex.I • peirceProjectorPlus := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp [gromovJStructure, Module.End.mul_apply]

/-- The $J$-structure acts with a negative sign on the negative chiral sector. -/
theorem gromovJStructure_peirce_minus :
    gromovJStructure * peirceProjectorMinus = (-Complex.I) • peirceProjectorMinus := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp [gromovJStructure, Module.End.mul_apply]

/-- The $J$-structure commutes with Peirce projectors. -/
theorem peirce_minus_gromovJStructure :
    peirceProjectorMinus * gromovJStructure = (-Complex.I) • peirceProjectorMinus := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp [gromovJStructure, Module.End.mul_apply]

/-- `J` anticommutes with the directed upper lightcone operator. -/
theorem gromov_witten_peirce_invariance (r : Fin 3) :
    gromovJStructure * lightconeSigmaPlus r = - (lightconeSigmaPlus r * gromovJStructure) := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  change gromovJStructure (lightconeSigmaPlus r (S, C)) =
    -(lightconeSigmaPlus r (gromovJStructure (S, C)))
  rw [lightconeSigmaPlus_apply, gromovJStructure_apply,
    gromovJStructure_apply, lightconeSigmaPlus_apply,
    CanonicalZornSpinChirality.cliffordMinus_neg,
    cliffordMinus_smul]
  simp

end ZornGromovWitten

end noncomputable section
