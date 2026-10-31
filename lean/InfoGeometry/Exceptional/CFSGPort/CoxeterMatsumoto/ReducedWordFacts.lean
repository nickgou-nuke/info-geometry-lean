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
module

public import Mathlib.GroupTheory.Coxeter.Inversion

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- A reduced word has no adjacent equal letters: deleting such a pair preserves its product and
shortens it. This is the small generic reduced-word fact needed by the ported rank-two argument. -/
theorem IsReduced.isChain_ne {ω : List B} (hω : cs.IsReduced ω) :
    ω.IsChain (· ≠ ·) := by
  revert hω
  induction ω with
  | nil => intro _; simp
  | cons a ρ ih =>
      cases ρ with
      | nil => intro _; simp
      | cons b τ =>
          intro hω
          have hρ : cs.IsReduced (b :: τ) := by simpa using hω.drop 1
          refine List.isChain_cons_cons.mpr ⟨?_, ih hρ⟩
          rintro rfl
          have hprod : cs.wordProd (a :: a :: τ) = cs.wordProd τ := by
            rw [cs.wordProd_cons, cs.wordProd_cons, cs.simple_mul_simple_cancel_left]
          have hle := cs.length_wordProd_le τ
          have heq := hω.eq
          rw [hprod] at heq
          simp only [List.length_cons] at heq
          omega

/-- A left descent prepends a letter to a reduced word for the corresponding shorter element. -/
theorem isReduced_cons_of_isLeftDescent {i : B} {w : W}
    (hd : cs.IsLeftDescent w i) {ω : List B} (hω : cs.IsReduced ω)
    (hprod : cs.wordProd ω = cs.simple i * w) : cs.IsReduced (i :: ω) := by
  have hw : cs.wordProd (i :: ω) = w := by
    rw [cs.wordProd_cons, hprod, cs.simple_mul_simple_cancel_left]
  have hlen : cs.length (cs.simple i * w) + 1 = cs.length w := cs.isLeftDescent_iff.mp hd
  rw [CoxeterSystem.IsReduced, hw, List.length_cons, ← hω.eq, hprod, hlen]

end CoxeterSystem

end
