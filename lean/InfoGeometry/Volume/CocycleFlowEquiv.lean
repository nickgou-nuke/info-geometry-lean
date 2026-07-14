import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# InfoGeometry.Volume.CocycleFlowEquiv

A minimal theorem-safe package for turning an additive one-parameter flow into
an equivalence.

The theorem is intentionally generic: it only uses the flow identity at `0`
and the additive composition law.  No analytic assumptions are introduced.
-/

set_option autoImplicit false
noncomputable section

namespace CocycleFlowEquiv

/--
A one-parameter additive flow is invertible at each time if it is normalized at
`0` and satisfies the additive composition law.
-/
noncomputable def cocycleFlowEquiv
    {Carrier : Type*}
    (flow : ℝ → Carrier → Carrier)
    (h_id : flow 0 = id)
    (h_comp : ∀ s t, flow (s + t) = flow s ∘ flow t)
    (t : ℝ) : Carrier ≃ Carrier where
  toFun := flow t
  invFun := flow (-t)
  left_inv x := by
    change (flow (-t) ∘ flow t) x = x
    rw [← h_comp (-t) t]
    have hneg : (-t : ℝ) + t = 0 := by
      simpa using (neg_add_cancel_left t 0)
    rw [hneg, h_id]
    rfl
  right_inv x := by
    change (flow t ∘ flow (-t)) x = x
    rw [← h_comp t (-t)]
    have hneg : (t : ℝ) + -t = 0 := by
      simpa using (neg_add_cancel_right t 0)
    rw [hneg, h_id]
    rfl

end CocycleFlowEquiv
