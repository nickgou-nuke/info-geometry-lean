import InfoGeometry.RootSystem.D4DualLattice
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exponent-two law for the `D₄` discriminant carrier

This owner proves the group-theoretic part of the discriminant calculation:
every class in `D₄* / D₄` is killed by two.  The cardinality-four and
triality statements are deliberately separate.
-/

namespace InfoGeometry.RootSystem.D4

theorem discriminantCarrier_add_self_eq_zero (x : dualSubgroup) :
    discriminantMap x + discriminantMap x = 0 := by
  let xd : DualLattice := ⟨x.1, x.2⟩
  rcases dual_integer_or_half_integer_normal_form xd with ⟨y, hy⟩ | ⟨y, hy⟩
  · let z : dualSubgroup :=
      ⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩
    have hxz : x = z := by
      apply Subtype.ext
      funext i
      exact hy i
    have hzz : z + z =
        (⟨integerEmbedding (2 • y),
          integerEmbedding_mem_dual_ambient (2 • y)⟩ : dualSubgroup) := by
      apply Subtype.ext
      funext i
      dsimp [z, integerEmbedding]
      change (y i : ℚ) + y i = ((2 • y) i : ℚ)
      rw [two_smul]
      change (y i : ℚ) + y i = ((y i + y i : ℤ) : ℚ)
      norm_num
    have hz : z + z ∈ integralSubgroup := by
      rw [hzz]
      exact two_integerEmbedding_mem_integralSubgroup y
    change QuotientAddGroup.mk' integralSubgroup (x + x) = 0
    apply (QuotientAddGroup.eq_zero_iff _).2
    simpa [hxz] using hz
  · let z : dualSubgroup :=
      ⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩
    let h : dualSubgroup := halfCoordinateSubgroup
    have hxzh : x = h + z := by
      apply Subtype.ext
      funext i
      exact hy i
    have hh : h + h ∈ integralSubgroup :=
      two_halfCoordinate_mem_integralSubgroup
    have hzz : z + z =
        (⟨integerEmbedding (2 • y),
          integerEmbedding_mem_dual_ambient (2 • y)⟩ : dualSubgroup) := by
      apply Subtype.ext
      funext i
      dsimp [z, integerEmbedding]
      change (y i : ℚ) + y i = ((2 • y) i : ℚ)
      rw [two_smul]
      change (y i : ℚ) + y i = ((y i + y i : ℤ) : ℚ)
      norm_num
    have hz : z + z ∈ integralSubgroup := by
      rw [hzz]
      exact two_integerEmbedding_mem_integralSubgroup y
    have hsum : (h + z) + (h + z) ∈ integralSubgroup := by
      rw [show (h + z) + (h + z) = (h + h) + (z + z) by abel]
      exact AddSubgroup.add_mem _ hh hz
    change QuotientAddGroup.mk' integralSubgroup (x + x) = 0
    apply (QuotientAddGroup.eq_zero_iff _).2
    simpa [hxzh] using hsum

end InfoGeometry.RootSystem.D4
