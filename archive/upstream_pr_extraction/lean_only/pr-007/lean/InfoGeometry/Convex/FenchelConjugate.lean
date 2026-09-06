import Mathlib.Analysis.Normed.Module.Basic

namespace InfoGeometry.Convex

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous dual. (You can also use `Dual ℝ E`.) -/
abbrev DualSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] ℝ

/-- Dual pairing map. -/
def dualPair (y : DualSpace E) (x : E) : ℝ :=
  y x

/-- Dual pairing (subscript to avoid clashing with inner-product notation). -/
local notation3 "⟪" y ", " x "⟫ₗ" => dualPair y x

/-- The set whose supremum defines the Fenchel conjugate. -/
def fenchelSet (f : E → ℝ) (y : DualSpace E) : Set ℝ :=
  Set.range (fun x : E => ⟪y, x⟫ₗ - f x)

/-- Fenchel conjugate defined as `sSup` over all affine minorants `⟪y,x⟫ - f x`. -/
noncomputable def fenchelConj (f : E → ℝ) (y : DualSpace E) : ℝ :=
  sSup (fenchelSet f y)

/-!
This real-valued `sSup` definition matches the usual Fenchel conjugate only
in the bounded-above regime (where `le_csSup`/`csSup` lemmas apply). Outside
that regime, conditionally complete `sSup` should be treated as unspecified.
For a fully general definition without boundedness side conditions, one usually
works in `EReal`.
-/

lemma fenchelSet_nonempty (f : E → ℝ) (y : DualSpace E) :
    (fenchelSet f y).Nonempty := by
  refine ⟨⟪y, (0 : E)⟫ₗ - f 0, ?_⟩
  exact ⟨0, rfl⟩

/-- Witness bound: `⟪y,x⟫ - f x ≤ f* y`, assuming bounded-above so `le_csSup` applies. -/
lemma le_fenchelConj (f : E → ℝ) (y : DualSpace E) (x : E)
    (hb : BddAbove (fenchelSet f y)) :
    ⟪y, x⟫ₗ - f x ≤ fenchelConj f y := by
  exact le_csSup hb ⟨x, rfl⟩

/-- Discoverability alias for `le_fenchelConj` in `≥` orientation. -/
lemma fenchelConj_ge_eval_sub (f : E → ℝ) (y : DualSpace E) (x : E)
    (hb : BddAbove (fenchelSet f y)) :
    fenchelConj f y ≥ ⟪y, x⟫ₗ - f x :=
  le_fenchelConj (f := f) (y := y) (x := x) hb

/-- Fenchel-Young inequality (real-valued version; needs `BddAbove` to use `le_csSup`). -/
theorem fenchelYoung (f : E → ℝ) (y : DualSpace E) (x : E)
    (hb : BddAbove (fenchelSet f y)) :
    ⟪y, x⟫ₗ ≤ f x + fenchelConj f y := by
  have h := le_fenchelConj (f := f) (y := y) (x := x) hb
  linarith

/-- Attainment packaged as a value equation gives equality in Fenchel-Young. -/
theorem fenchelYoung_eq_of_conj_eq (f : E → ℝ) (y : DualSpace E) (x : E)
    (h : fenchelConj f y = ⟪y, x⟫ₗ - f x) :
    ⟪y, x⟫ₗ = f x + fenchelConj f y := by
  linarith

/-- If `⟪y,x⟫ - f x` is a greatest element of the defining set, then it attains `sSup`. -/
theorem fenchelConj_eq_of_isGreatest (f : E → ℝ) (y : DualSpace E) (x : E)
    (hG : IsGreatest (fenchelSet f y) (⟪y, x⟫ₗ - f x)) :
    fenchelConj f y = ⟪y, x⟫ₗ - f x := by
  simpa [fenchelConj] using
    (hG.csSup_eq : sSup (fenchelSet f y) = (⟪y, x⟫ₗ - f x))

end InfoGeometry.Convex
