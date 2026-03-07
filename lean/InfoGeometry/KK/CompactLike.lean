import Mathlib.Data.Real.Basic

/-!
# InfoGeometry.KK.CompactLike

Minimal compactness-like interface for the bounded Kasparov layer.
This is intentionally algebraic and can be refined later to genuine
compact-operator predicates.
-/

namespace InfoGeometry.KK

/-- Abstract closure axioms for a compactness-like predicate on operators. -/
class CompactLike {Op : Type*} [Zero Op] [Add Op] [SMul ℝ Op] (K : Op → Prop) : Prop where
  zero_mem : K 0
  add_mem : ∀ {A B : Op}, K A → K B → K (A + B)
  smul_mem : ∀ {r : ℝ} {A : Op}, K A → K (r • A)

end InfoGeometry.KK

