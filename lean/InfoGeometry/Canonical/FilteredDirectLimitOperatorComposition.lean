/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FilteredDirectLimitOperator

noncomputable section

namespace InfoGeometry.Canonical.FilteredDirectLimitOperator

universe u

variable
    (Stage : ℕ → Type u)
    [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)

namespace CompatibleOperatorFamily

/-- Pointwise composition of two compatible additive stage families. -/
def compose
    (F G : CompatibleOperatorFamily Stage f) :
    CompatibleOperatorFamily Stage f where
  op := fun n => (F.op n).comp (G.op n)
  commutes := by
    intro m n h x
    change F.op n (G.op n (f m n h x)) =
      f m n h (F.op m (G.op m x))
    rw [G.commutes m n h x, F.commutes m n h (G.op m x)]

/-- Composition commutes with the canonical direct-limit lift. -/
theorem directLimitOperator_compose
    (F G : CompatibleOperatorFamily Stage f) :
    directLimitOperator Stage f (compose Stage f F G) =
      (directLimitOperator Stage f F).comp
        (directLimitOperator Stage f G) := by
  apply AddMonoidHom.ext
  intro z
  induction z using AddCommGroup.DirectLimit.induction_on with
  | _ n x =>
      rw [directLimitOperator_of Stage f (compose Stage f F G) n x]
      change
        AddCommGroup.DirectLimit.of Stage f n ((compose Stage f F G).op n x) =
          directLimitOperator Stage f F
            (directLimitOperator Stage f G
              (AddCommGroup.DirectLimit.of Stage f n x))
      rw [directLimitOperator_of Stage f G n x]
      rw [directLimitOperator_of Stage f F n]
      rfl

end CompatibleOperatorFamily

end InfoGeometry.Canonical.FilteredDirectLimitOperator
