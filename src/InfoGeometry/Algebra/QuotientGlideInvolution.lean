import Mathlib.GroupTheory.QuotientGroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Involutions after quotienting translations

The affine/glide mechanism used by wallpaper groups has a small generic
group-theoretic core: an element whose square lies in the quotient subgroup
becomes an involution in the quotient.  This file records only that core;
it does not assert any particular wallpaper or Weyl-group identification.
-/

namespace InfoGeometry.Algebra.QuotientGlideInvolution

theorem quotient_sq_eq_one_of_sq_mem
    {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal]
    (g : G)
    (hg : g ^ 2 ∈ N) :
    (QuotientGroup.mk g : G ⧸ N) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hg

end InfoGeometry.Algebra.QuotientGlideInvolution
