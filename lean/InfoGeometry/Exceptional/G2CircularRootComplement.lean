/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2CircularRootLabelTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Exceptional.G2CircularRootComplement

open InfoGeometry.Exceptional.G2CircularRootLabelTransport

abbrev RootLabel := InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.G2CoordinateRoot

def circularRootComplement : Finset RootLabel :=
  Finset.univ.filter (fun r => ∀ i : CircularLabel,
    circularRootTransport.label i ≠ r)

theorem circularRootComplement_card :
    (circularRootComplement).card = 4 := by
  native_decide

theorem mem_circularRootComplement_iff (r : RootLabel) :
    r ∈ circularRootComplement ↔
      ∀ i : CircularLabel, circularRootTransport.label i ≠ r := by
  simp [circularRootComplement]

end InfoGeometry.Exceptional.G2CircularRootComplement
