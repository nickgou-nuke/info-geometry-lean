/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# The two-state left action of a Peirce nilpotent pair

For the associative Peirce carrier, `N₊` and `Q₋ = N₋N₊` are two elements
of the right `(1-P)` corner.  This file records the exact generator action on
those elements.  The coefficient in `N₊ Q₋ = V N₊` is the operator `V`, not
a scalar, so this identity alone does not identify projective rays.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

theorem qgtMinus_mul_P {P : B} (hP : P * P = P) (A C : B) :
    qgtMinus P A C * P = 0 := by
  simp only [qgtMinus]
  peirce_nf hP

theorem conePlus_mul_qgtMinus {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * qgtMinus P A C =
      genV P A C * conePlus P A := by
  simp only [qgtMinus]
  peirce_nf hP

theorem coneMinus_mul_qgtMinus {P : B} (hP : P * P = P) (A C : B) :
    coneMinus P C * qgtMinus P A C = 0 := by
  simp only [qgtMinus]
  peirce_nf hP

theorem genPhi_mul_conePlus {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * conePlus P A = qgtMinus P A C := by
  simp only [qgtMinus]
  peirce_nf hP

theorem genPhi_mul_qgtMinus {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * qgtMinus P A C =
      genV P A C * conePlus P A := by
  simp only [qgtMinus]
  peirce_nf hP

theorem genJ_mul_conePlus {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * conePlus P A = -qgtMinus P A C := by
  simp only [qgtMinus]
  peirce_nf hP

theorem genJ_mul_qgtMinus {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * qgtMinus P A C =
      genV P A C * conePlus P A := by
  simp only [qgtMinus]
  peirce_nf hP

theorem genSig_mul_conePlus {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * conePlus P A =
      genV P A C * conePlus P A := by
  peirce_nf hP

theorem genSig_mul_qgtMinus {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * qgtMinus P A C =
      -(genV P A C * qgtMinus P A C) := by
  simp only [qgtMinus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
