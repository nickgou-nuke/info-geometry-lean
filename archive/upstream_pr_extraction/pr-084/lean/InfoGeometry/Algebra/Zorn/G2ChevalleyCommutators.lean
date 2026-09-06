/- SPDX-FileCopyrightText: 2024-2026 The InfoGeometry Authors
SPDX-License-Identifier: MIT -/

import InfoGeometry.Algebra.Zorn.G2PCCommutators

/-!
# PC commutator boundary for the finite G2(2) carrier

This file exposes only the already-certified polycyclic commutator boundary.
It does not promote the PC generators to root subgroups: that identification
requires additional native root-word equalities.
-/

namespace InfoGeometry.Algebra.Zorn.Chevalley

open InfoGeometry.Algebra.Zorn.G2PC
open InfoGeometry.Algebra.Zorn.G2PCCollection

/-- The first nontrivial certified PC commutator, in its native coordinate form. -/
theorem pc_commutator_zero_one :
    pcComm 0 1 = fun k => match k with
      | 2 => 1
      | 3 => 1
      | 5 => 1
      | _ => 0 := by
  rfl

/-- The maximal PC generator is central in the certified commutator table. -/
theorem pc_commutator_maximal_central (i : Fin 6) :
    pcComm i 5 = zeroExp :=
  e5_is_central i

end InfoGeometry.Algebra.Zorn.Chevalley
