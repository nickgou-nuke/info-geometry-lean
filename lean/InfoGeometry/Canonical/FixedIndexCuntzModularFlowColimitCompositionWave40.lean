/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open FilteredColimit.Native

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)
variable (Φ : FlowData Stage T)

/-- The descended modular flow composes in the forward time order.

The owner-level descent theorem stores the categorical composition in the
opposite syntactic order, because `CategoryStruct.comp` composes right to
left.  Commutativity of addition in `ℝ` converts that universal-property
statement into the usual forward-time semigroup law.
-/
theorem flowColimitMap_comp_wave40 (t s : ℝ) :
    flowColimitMap Stage T Φ t ≫ flowColimitMap Stage T Φ s =
      flowColimitMap Stage T Φ (t + s) := by
  calc
    flowColimitMap Stage T Φ t ≫ flowColimitMap Stage T Φ s =
        flowColimitMap Stage T Φ (s + t) :=
      (flowColimitMap_add Stage T Φ s t).symm
    _ = flowColimitMap Stage T Φ (t + s) := by rw [add_comm s t]

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
