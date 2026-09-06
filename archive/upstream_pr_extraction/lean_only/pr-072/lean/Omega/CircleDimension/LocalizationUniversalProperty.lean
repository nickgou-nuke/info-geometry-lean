import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Basic

namespace Omega.CircleDimension

/-- Native localization universal property: a ring map out of a localization is uniquely
determined by its restriction to the base ring, provided the chosen denominators map to units. -/
theorem native_localization_universal_property
    {R S P : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring P]
    {M : Submonoid R} [Algebra R S] [Algebra R P] [IsLocalization M S]
    (g : R →+* P) (hg : ∀ y : M, IsUnit (g y)) :
    ∃! j : S →+* P, ∀ x : R, j (algebraMap R S x) = g x := by
  refine ⟨IsLocalization.lift hg, ?_, ?_⟩
  · intro x
    rw [← IsLocalization.mk'_one (M := M) S x]
    rw [IsLocalization.lift_mk' (M := M) hg]
    simp
  · intro j hj
    exact (IsLocalization.lift_unique (M := M) hg hj).symm

end Omega.CircleDimension
