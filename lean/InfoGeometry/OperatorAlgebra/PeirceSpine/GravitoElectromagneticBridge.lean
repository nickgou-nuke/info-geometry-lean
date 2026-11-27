/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Gravito-electromagnetic Peirce identities

The declarations below are finite identities in an associative ring. Their
names provide context; no physical or transport interpretation is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The Peirce corner commutator and grading-weighted Jordan product agree. -/
theorem gemDipole_chiral_lock {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C - invS P * genV P A C = 0 := by
  peirce_nf hP

/-- First-order commutator of the Peirce spin and solder operators. -/
theorem gemFirstOrderLenseThirring {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) := by
  peirce_nf hP

/-- Dual first-order commutator of the Peirce spin and skew operators. -/
theorem gemDualPrecession {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genJ P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) := by
  peirce_nf hP

/-- Commutator of the Peirce spin with the upper corner. -/
theorem gemCornerPrecession_plus {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) := by
  peirce_nf hP

/-- Commutator of the Peirce spin with the lower corner. -/
theorem gemCornerPrecession_minus {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (coneMinus P C) =
      -((2 : ℤ) • (genV P A C * coneMinus P C)) := by
  peirce_nf hP

/-- Second-order double commutator of the Peirce spin on the solder operator. -/
theorem gemSecondOrderCentrifugal {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) := by
  peirce_nf hP

/-- Dual second-order double commutator of the Peirce spin on the skew operator. -/
theorem gemSecondOrderCentrifugal_dual {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) := by
  peirce_nf hP

/-- The Peirce spin anticommutes with the solder operator. -/
theorem gemSpinPhi_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genSig P A C) (genPhi P A C) = 0 := by
  peirce_nf hP

/-- The Peirce spin anticommutes with the skew operator. -/
theorem gemSpinJ_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genSig P A C) (genJ P A C) = 0 := by
  peirce_nf hP

/-- The first-order Peirce force is anticommuting with the solder operator. -/
theorem gemWorkFreeCoriolis {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genPhi P A C)
      (comm (genSig P A C) (genPhi P A C)) = 0 := by
  peirce_nf hP

/-- Ordered product of the Peirce spin and solder operators. -/
theorem gemSpinMulPhi_eq {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * genPhi P A C = genV P A C * genJ P A C := by
  peirce_nf hP

/-- Square of the ordered spin-solder product. -/
theorem gemNilpotentCollapse {P : B} (hP : P * P = P) (A C : B) :
    (genSig P A C * genPhi P A C) * (genSig P A C * genPhi P A C) =
      -(genV P A C * genV P A C * genV P A C) := by
  peirce_nf hP

/-- The two Peirce first-order commutators anticommute. -/
theorem gemOnsagerReciprocity_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (comm (genSig P A C) (genPhi P A C))
      (comm (genSig P A C) (genJ P A C)) = 0 := by
  peirce_nf hP

/-- Difference of squares of the two Peirce first-order commutators. -/
theorem gemOnsagerReciprocity_sq_diff {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genPhi P A C) * comm (genSig P A C) (genPhi P A C) -
        comm (genSig P A C) (genJ P A C) * comm (genSig P A C) (genJ P A C) =
      -((8 : ℤ) • (genV P A C * genV P A C * genV P A C)) := by
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
