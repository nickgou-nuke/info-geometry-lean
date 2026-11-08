/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

noncomputable section

namespace InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (E : I → Type u)
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E)

/-- The canonical completed colimit embedding preserves the stage inner product. -/
theorem stageToHilbertDirectLimit_inner
    (i : I) (x y : E i) :
    inner ℂ
      (stageToHilbertDirectLimit E sys i x)
      (stageToHilbertDirectLimit E sys i y) =
      inner ℂ x y := by
  exact (stageToHilbertDirectLimit E sys i).inner_map_map x y

end InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
