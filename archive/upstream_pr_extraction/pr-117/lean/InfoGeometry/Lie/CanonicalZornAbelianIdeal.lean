import InfoGeometry.Lie.CanonicalZornMathlibBridge
import Mathlib.Algebra.Lie.Abelian

/-!
# Structural consequences for abelian ideals

This owner records the two elementary ideal-theoretic reductions used in the
semisimplicity argument.  It deliberately does not assert that every abelian
ideal is zero: that stronger statement still needs a proved invariant-ideal
decomposition and nonzero opposite-root brackets for the concrete Zorn basis.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornAbelianIdeal

open InfoGeometry.Lie.CanonicalZornMathlibBridge
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

abbrev Der := CanonicalZornCartanRootSystem.Der

/-- An abelian ideal annihilates every pair of its elements. -/
theorem abelianIdeal_bracket_eq_zero
    (I : LieIdeal ℝ Der) [hI : IsLieAbelian I]
    (x y : I) : ⁅(x : Der), (y : Der)⁆ = 0 := by
  exact congrArg Subtype.val (hI.trivial x y)

/-- Two ideal elements with a nonzero ambient bracket contradict abelianity. -/
theorem abelianIdeal_excludes_nonzero_bracket
    (I : LieIdeal ℝ Der) [hI : IsLieAbelian I]
    {x y : I} (hxy : ⁅(x : Der), (y : Der)⁆ ≠ 0) : False := by
  exact hxy (abelianIdeal_bracket_eq_zero I x y)

/-- Ideal closure transports a root vector bracket back into the ideal. -/
theorem ideal_mem_bracket_of_mem
    (I : LieIdeal ℝ Der) {D : Der} (hD : D ∈ I) (X : Der) :
    ⁅X, D⁆ ∈ I := by
  exact lie_mem_right ℝ Der I X D hD

/-- A nontrivial Cartan action on an ideal element is incompatible with an
abelian ideal when the acting Cartan element is itself in that ideal. -/
theorem abelianIdeal_excludes_nontrivial_root_action
    (I : LieIdeal ℝ Der) [hI : IsLieAbelian I]
    {H X : I} (hHX : ⁅(H : Der), (X : Der)⁆ ≠ 0) : False := by
  exact abelianIdeal_excludes_nonzero_bracket I hHX

end InfoGeometry.Lie.CanonicalZornAbelianIdeal
