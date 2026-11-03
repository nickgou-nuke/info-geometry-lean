/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralDifferentials

/-!
# Graded derivations on the Peirce generators

The generator identities in source A₃₁. These are evaluations in an
arbitrary ring. The square-zero restriction and its additive cohomology
are constructed separately in CentralizerDifferential and CentralizerCohomology;
no de Rham complex of a manifold is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

theorem superDerivPlusBar_invS (A : B) :
    superDerivPlusBar P A (invS P) = 0 := by
  simp only [superDerivPlusBar, parityConj]
  peirce_nf hP

theorem superDerivMinusBar_invS (C : B) :
    superDerivMinusBar P C (invS P) = 0 := by
  simp only [superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivPhi_invS (A C : B) :
    superDerivPhi P A C (invS P) = -((2 : ℤ) • genJ P A C) := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivJ_invS (A C : B) :
    superDerivJ P A C (invS P) = -((2 : ℤ) • genPhi P A C) := by
  simp only [superDerivJ, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivPhi_genPhi (A C : B) :
    superDerivPhi P A C (genPhi P A C) = (2 : ℤ) • genV P A C := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivJ_genJ (A C : B) :
    superDerivJ P A C (genJ P A C) = -((2 : ℤ) • genV P A C) := by
  simp only [superDerivJ, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivJBar_genPhi (A C : B) :
    superDerivJBar P A C (genPhi P A C) = (2 : ℤ) • genSig P A C := by
  simp only [superDerivJBar, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivPhiBar_genJ (A C : B) :
    superDerivPhiBar P A C (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  simp only [superDerivPhiBar, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivPlus_genV (A C : B) :
    superDerivPlus P A (genV P A C) = 0 := by
  simp only [superDerivPlus, parityConj]
  peirce_nf hP

theorem superDerivMinus_genV (A C : B) :
    superDerivMinus P C (genV P A C) = 0 := by
  simp only [superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivPhi_genV (A C : B) :
    superDerivPhi P A C (genV P A C) = 0 := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

/-- The generator action relevant to the proposed obstruction-killing
interpretation. The unit is closed, but the cut `P` is sent to `-J`, so this
operator is not zero on the proposed base span `{1, P}`. It sends `Φ` to `2V`
and annihilates `V`; its square is a differential only after restriction to
the centralizer of `V` (see `CentralizerDifferential`). -/
theorem superDerivPhi_core_and_tetraktys_action (A C : B) :
    superDerivPhi P A C 1 = 0 ∧
    superDerivPhi P A C P = -genJ P A C ∧
    superDerivPhi P A C (genPhi P A C) = (2 : ℤ) • genV P A C ∧
    superDerivPhi P A C (genV P A C) = 0 := by
  refine ⟨?_, ?_, superDerivPhi_genPhi hP A C, superDerivPhi_genV hP A C⟩
  · simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
    peirce_nf hP
  · simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
    peirce_nf hP

theorem superDerivJ_genV (A C : B) :
    superDerivJ P A C (genV P A C) = 0 := by
  simp only [superDerivJ, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivPlusBar_genSig (A C : B) :
    superDerivPlusBar P A (genSig P A C) = 0 := by
  simp only [superDerivPlusBar, parityConj]
  peirce_nf hP

theorem superDerivMinusBar_genSig (A C : B) :
    superDerivMinusBar P C (genSig P A C) = 0 := by
  simp only [superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivJBar_genSig (A C : B) :
    superDerivJBar P A C (genSig P A C) = 0 := by
  simp only [superDerivJBar, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivPhi_genJ (A C : B) :
    superDerivPhi P A C (genJ P A C) = 0 := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivJ_genPhi (A C : B) :
    superDerivJ P A C (genPhi P A C) = 0 := by
  simp only [superDerivJ, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivPhi_square_invS (A C : B) :
    superDerivPhi P A C (superDerivPhi P A C (invS P)) = 0 := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

theorem superDerivJ_square_invS (A C : B) :
    superDerivJ P A C (superDerivJ P A C (invS P)) = 0 := by
  simp only [superDerivJ, superDerivPlus, superDerivMinus, parityConj]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
