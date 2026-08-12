import Mathlib.RingTheory.OreLocalization.Basic

/-!
  The Ore-set data for localization by the whole monoid.  This owner contains
  only the native Ore condition; a group structure on the localization is not
  asserted without the corresponding current Mathlib construction.
-/

class CommonLeftMultipleMonoid (M : Type*) extends Monoid M where
  cl₁ : M → M → M
  cl₂ : M → M → M
  cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b

class OreMonoid (M : Type*) extends CommonLeftMultipleMonoid M, CancelMonoid M

variable {M : Type*} [OreMonoid M]

instance oreSetSelf : OreLocalization.OreSet (⊤ : Submonoid M) where
  ore_right_cancel := by
    intro r₁ r₂ s h
    refine ⟨1, ?_⟩
    simpa using (mul_right_cancel h)
  oreNum r s := CommonLeftMultipleMonoid.cl₁ r s
  oreDenom r s := ⟨CommonLeftMultipleMonoid.cl₂ r s, trivial⟩
  ore_eq := by
    intro r s
    simpa using (CommonLeftMultipleMonoid.cl_spec r (s : M))
