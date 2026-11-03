/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

/-- Model data for a finite residue carrier. No compact-Lie or profinite reduction is encoded. -/
structure conclusion_compact_lie_profinite_kernel_obstruction_data where
  kernelCard : Nat

/-- The finite carrier chosen for the residue model. -/
abbrev conclusion_compact_lie_profinite_kernel_obstruction_data.kernel
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) : Type :=
  Fin D.kernelCard

/-- The cardinality of the model kernel is exactly its declared residue size. -/
theorem conclusion_compact_lie_profinite_kernel_obstruction_data.kernel_card
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) :
    Fintype.card D.kernel = D.kernelCard := by
  exact Fintype.card_fin D.kernelCard

/-- The finite kernel conclusion. -/
def conclusion_compact_lie_profinite_kernel_obstruction_data.kernelFinite
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) : Prop :=
  Nonempty (Fintype D.kernel)

/-- Paper label: `thm:conclusion-compact-lie-profinite-kernel-obstruction`. The encoded conclusion
is only that the chosen `Fin kernelCard` carrier is finite; no compact-Lie or profinite object is
constructed here. -/
theorem paper_conclusion_compact_lie_profinite_kernel_obstruction
    (D : conclusion_compact_lie_profinite_kernel_obstruction_data) : D.kernelFinite := by
  exact ⟨inferInstance⟩

end Omega.Conclusion
