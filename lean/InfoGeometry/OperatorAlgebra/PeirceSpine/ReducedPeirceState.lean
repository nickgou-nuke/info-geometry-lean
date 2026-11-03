/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.UHFHeisenbergSugawaraVirasoroPoset

/-!
# Reduced diagonal corners of a two-sided Peirce shear

These identities concern algebraic corner projections and idempotency defects.
They do not assert positivity, a trace, or an entropy interpretation.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def boundaryBruhat (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C)

def boundaryBruhatInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A)

/-- Reverse-order two-factor transform, dual to `boundaryBruhat`. -/
def boundaryBruhatDual (P A C : B) : B :=
  (1 - coneMinus P C) * (1 + conePlus P A)

/-- Explicit inverse of `boundaryBruhatDual`. -/
def boundaryBruhatDualInv (P A C : B) : B :=
  (1 - conePlus P A) * (1 + coneMinus P C)

/-- The reverse-order Bruhat transform is invertible, and its difference from
the forward transform is the negative Peirce commutator. -/
theorem boundaryBruhatDual_inverse_and_order_defect
    (P A C : B) (hP : P * P = P) :
    boundaryBruhatDual P A C * boundaryBruhatDualInv P A C = 1 ∧
    boundaryBruhatDualInv P A C * boundaryBruhatDual P A C = 1 ∧
    boundaryBruhat P A C - boundaryBruhatDual P A C = -genSig P A C := by
  simp only [boundaryBruhat, boundaryBruhatDual, boundaryBruhatDualInv,
    genSig, comm, conePlus, coneMinus]
  peirce_nf hP <;> simp

def coupledPeirceState (P A C : B) : B :=
  boundaryBruhat P A C * P * boundaryBruhatInv P A C

def reducedUpperState (P A C : B) : B :=
  peirce11 P (coupledPeirceState P A C)

def reducedLowerState (P A C : B) : B :=
  peirce00 P (coupledPeirceState P A C)

/-- The two-sided shear is invertible, its conjugate of `P` is idempotent,
and its diagonal corner projections are `P - Q₊` and `Q₋`. The two corner
defects add to the defect of `V`. -/
theorem reduced_peirce_state_and_defect
    {P : B} (hP : P * P = P) (A C : B) :
    boundaryBruhat P A C * boundaryBruhatInv P A C = 1 ∧
    boundaryBruhatInv P A C * boundaryBruhat P A C = 1 ∧
    coupledPeirceState P A C * coupledPeirceState P A C =
      coupledPeirceState P A C ∧
    reducedUpperState P A C = P - qgtPlus P A C ∧
    reducedLowerState P A C = qgtMinus P A C ∧
    (P - reducedUpperState P A C) + reducedLowerState P A C =
      genV P A C ∧
    (P - reducedUpperState P A C) - reducedLowerState P A C =
      genSig P A C ∧
    idemDefect (reducedUpperState P A C) +
      idemDefect (reducedLowerState P A C) = idemDefect (genV P A C) := by
  have hInv : boundaryBruhat P A C * boundaryBruhatInv P A C = 1 := by
    simp only [boundaryBruhat, boundaryBruhatInv, conePlus, coneMinus]
    peirce_nf hP
  have hInv' : boundaryBruhatInv P A C * boundaryBruhat P A C = 1 := by
    simp only [boundaryBruhat, boundaryBruhatInv, conePlus, coneMinus]
    peirce_nf hP
  have hState : coupledPeirceState P A C * coupledPeirceState P A C =
      coupledPeirceState P A C := by
    simp only [coupledPeirceState]
    calc
      (boundaryBruhat P A C * P * boundaryBruhatInv P A C) *
          (boundaryBruhat P A C * P * boundaryBruhatInv P A C) =
          boundaryBruhat P A C * (P * (boundaryBruhatInv P A C *
            boundaryBruhat P A C) * P) * boundaryBruhatInv P A C := by noncomm_ring
      _ = boundaryBruhat P A C * P * boundaryBruhatInv P A C := by rw [hInv', mul_one, hP]
  have hUpper : reducedUpperState P A C = P - qgtPlus P A C := by
    simp only [reducedUpperState, coupledPeirceState, boundaryBruhat,
      boundaryBruhatInv, peirce11, qgtPlus, conePlus, coneMinus]
    peirce_nf hP
  have hLower : reducedLowerState P A C = qgtMinus P A C := by
    simp only [reducedLowerState, coupledPeirceState, boundaryBruhat,
      boundaryBruhatInv, peirce00, qgtMinus, conePlus, coneMinus]
    peirce_nf hP
  have hMass : (P - reducedUpperState P A C) + reducedLowerState P A C =
      genV P A C := by rw [hUpper, hLower]; peirce_nf hP
  have hSpin : (P - reducedUpperState P A C) - reducedLowerState P A C =
      genSig P A C := by rw [hUpper, hLower]; peirce_nf hP
  have hDef : idemDefect (reducedUpperState P A C) +
      idemDefect (reducedLowerState P A C) = idemDefect (genV P A C) := by
    rw [hUpper, hLower]
    simp only [idemDefect, qgtPlus, qgtMinus, genV, anticomm, conePlus, coneMinus]
    peirce_nf hP
  exact ⟨hInv, hInv', hState, hUpper, hLower, hMass, hSpin, hDef⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
