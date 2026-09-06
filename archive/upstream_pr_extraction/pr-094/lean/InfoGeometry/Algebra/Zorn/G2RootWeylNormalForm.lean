/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

/-!
# The root-side transport of the existing dihedral normal-form index

This owner deliberately reuses `WeylG2 := ZMod 6 × Bool`.  It does not define
a second Weyl group or a second multiplication law.  Its purpose is only to
transport the already existing normal-form index to the signed coordinate
root carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm

open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge

def rootWeylNF (p : WeylG2) : Equiv.Perm G2CoordinateRoot :=
  if p.2 then s1Root.trans (cRoot ^ p.1.val) else cRoot ^ p.1.val

@[simp] theorem rootWeylNF_eq_coordinateWeylAction (p : WeylG2) :
    rootWeylNF p = coordinateWeylAction p := rfl

@[simp] theorem rootWeylNF_one : rootWeylNF (0, false) = 1 := by
  simp [rootWeylNF]

@[simp] theorem rootWeylNF_cyclic_one :
    rootWeylNF (1, false) = cRoot := by
  change cRoot ^ (1 : ℕ) = cRoot
  simp

end InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm
