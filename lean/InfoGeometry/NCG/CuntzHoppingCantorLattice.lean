/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import Mathlib.Tactic

/-!
# Cuntz shift and finite binary addresses

This module reuses the repository's `CuntzSystem` and its canonical shift.
The algebraic shift results below concern an associative star ring. Finite
binary-word prefixing is a separate combinatorial operation; no representation
of the Cuntz algebra on Cantor addresses is asserted here.
-/

namespace InfoGeometry.NCG.CuntzHoppingCantorLattice

open InfoGeometry.NCG
open scoped BigOperators

variable {Op : Type*} [Ring Op] [StarRing Op]
variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
variable (C : CuntzSystem (Fin n) Op)

/-- Prefix a finite Cantor address by the bit represented by `i : Fin 2`. -/
def prefixAddress (i : Fin 2)
    (w : InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord) :
    InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord :=
  (if i = 0 then false else true) :: w

/-- The generator label belonging to a Cuntz index. This does not itself act
on a binary address; `prefixAddress` records the corresponding word operation. -/
def hopGenerator (i : Fin n) : Op := C.S i

/-- The canonical Cuntz shift, inherited from the shared owner definition. -/
abbrev cuntzShiftHopping (X : Op) : Op := C.canonicalShift X

theorem cuntzShiftHopping_one : cuntzShiftHopping C (1 : Op) = 1 := by
  exact C.canonicalShift_one

theorem cuntzCompleteness_partitionOfUnity :
    (∑ i : Fin n, C.S i * star (C.S i)) = 1 := by
  exact C.completeness'

theorem cuntzHopping_orthogonalChildSectors {i j : Fin n} (hij : i ≠ j) :
    star (C.S i) * C.S j = 0 := by
  have h := C.isometry' i j
  simp [hij] at h
  exact h

theorem cuntzShiftHopping_star (X : Op) :
    cuntzShiftHopping C (star X) = star (cuntzShiftHopping C X) := by
  exact C.canonicalShift_star X

theorem cuntzShiftHopping_mul (X Y : Op) :
    cuntzShiftHopping C (X * Y) = cuntzShiftHopping C X * cuntzShiftHopping C Y := by
  exact C.canonicalShift_mul X Y

theorem cuntzShiftHopping_intertwines (j : Fin n) (X : Op) :
    star (C.S j) * cuntzShiftHopping C X = X * star (C.S j) := by
  exact C.shift_intertwines j X

end InfoGeometry.NCG.CuntzHoppingCantorLattice
