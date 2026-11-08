/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-! Exact Peirce-grading product identities in an associative ring. -/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The grading-twisted product of `P + Φ` retains the odd term `-J`
and the contributions from both diagonal corners. -/
theorem grading_norm_cut_add_phi {P : B} (hP : P * P = P) (A C : B) :
    (P + genPhi P A C) * (invS P * (P + genPhi P A C) * invS P) =
      P - genJ P A C - genV P A C := by
  simp only [invS, genPhi, genJ, genV, anticomm, conePlus, coneMinus]
  peirce_nf hP

/-- The sign of the commutator follows from the ordered corner products. -/
theorem phi_j_comm_sign {P : B} (hP : P * P = P) (A C : B) :
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  simp only [comm, genPhi, genJ, genSig, conePlus, coneMinus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
