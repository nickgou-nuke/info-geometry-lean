/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Parity intertwiners for the tetraktys double commutators

The Peirce commutator exchanges the two odd generators `Φ` and `J`. On the
full associative ring it consequently intertwines the corresponding signed
second commutators. These are algebraic identities; no dynamics is assumed.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
include hP

/-- The Peirce commutator intertwines the `Φ` and `J` double derivations. -/
theorem peirce_comm_derivSqPhi_intertwines_J :
    comm P (derivSqPhi P A C X) =
      derivSqJ P A C (comm P X) := by
  simp only [derivSqPhi, derivSqJ]
  peirce_nf hP

/-- The reverse intertwining follows with the roles of `Φ` and `J` exchanged. -/
theorem peirce_comm_derivSqJ_intertwines_Phi :
    comm P (derivSqJ P A C X) =
      derivSqPhi P A C (comm P X) := by
  simp only [derivSqPhi, derivSqJ]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
