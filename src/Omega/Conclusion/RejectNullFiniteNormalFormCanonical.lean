/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The six alternatives in the finite rejection classification. -/
def RejectNullFiniteClass (semanticNull protocolNull collisionNull defRad defDepth defEndpoint : Prop) :
    Prop :=
  semanticNull ∨ protocolNull ∨ collisionNull ∨ defRad ∨ defDepth ∨ defEndpoint

/-- The null classification implies the corresponding branch of the six-way disjunction. -/
theorem rejectNullFiniteNormalForm_of_classifications
    (semanticNull protocolNull collisionNull defRad defDepth defEndpoint : Prop)
    (hnull : semanticNull ∨ protocolNull ∨ collisionNull) :
    RejectNullFiniteClass semanticNull protocolNull collisionNull defRad defDepth defEndpoint := by
  rcases hnull with hSemantic | hProtocol | hCollision
  · exact Or.inl hSemantic
  · exact Or.inr (Or.inl hProtocol)
  · exact Or.inr (Or.inr (Or.inl hCollision))

/-- Both supplied classification branches are retained in the paired normal form. -/
theorem rejectNullFinitePairedNormalForm
    (semanticNull protocolNull collisionNull defRad defDepth defEndpoint : Prop)
    (hnull : semanticNull ∨ protocolNull ∨ collisionNull)
    (hdef : defRad ∨ defDepth ∨ defEndpoint) :
    (semanticNull ∨ protocolNull ∨ collisionNull) ∧
      (defRad ∨ defDepth ∨ defEndpoint) ∧
      RejectNullFiniteClass semanticNull protocolNull collisionNull defRad defDepth defEndpoint := by
  exact ⟨hnull, hdef,
    rejectNullFiniteNormalForm_of_classifications semanticNull protocolNull collisionNull
      defRad defDepth defEndpoint hnull⟩

/-- Pairwise exclusivity of the three null alternatives. -/
theorem rejectNullAlternatives_exclusive
    (semanticNull protocolNull collisionNull : Prop)
    (hsem : semanticNull → ¬ protocolNull ∧ ¬ collisionNull)
    (hprot : protocolNull → ¬ semanticNull ∧ ¬ collisionNull) :
    ¬ (semanticNull ∧ protocolNull) ∧
      ¬ (semanticNull ∧ collisionNull) ∧
      ¬ (protocolNull ∧ collisionNull) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hs, hp⟩
    exact (hsem hs).1 hp
  · rintro ⟨hs, hc⟩
    exact (hsem hs).2 hc
  · rintro ⟨hp, hc⟩
    exact (hprot hp).2 hc

/-- Pairwise exclusivity of the three defect-budget alternatives. -/
theorem rejectNullDefects_exclusive
    (defRad defDepth defEndpoint : Prop)
    (hrad : defRad → ¬ defDepth ∧ ¬ defEndpoint)
    (hdepth : defDepth → ¬ defRad ∧ ¬ defEndpoint) :
    ¬ (defRad ∧ defDepth) ∧
      ¬ (defRad ∧ defEndpoint) ∧
      ¬ (defDepth ∧ defEndpoint) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hr, hd⟩
    exact (hrad hr).1 hd
  · rintro ⟨hr, he⟩
    exact (hrad hr).2 he
  · rintro ⟨hd, he⟩
    exact (hdepth hd).2 he

end Omega.Conclusion
