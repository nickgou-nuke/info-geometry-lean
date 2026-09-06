import InfoGeometry.RootSystem.D4DualLattice

/-!
# The four explicit discriminant representatives for `D₄`

This owner proves the exhaustive coset statement.  It does not yet identify
the quotient with a chosen finite group or construct triality.
-/

namespace InfoGeometry.RootSystem.D4

theorem d4_dual_adjusted_integer_mem (y : Ambient) (hy : ¬ IsD4 y) :
    IsD4 (y - basisVector 0) := by
  change coordinateSum (y - basisVector 0) % 2 = 0
  rw [coordinateSum_sub, coordinateSum_basisVector_zero]
  have h := hy
  change coordinateSum y % 2 ≠ 0 at h
  omega

theorem d4_dual_adjusted_half_mem (y : Ambient) (hy : ¬ IsD4 y) :
    IsD4 (y - negativeThirdBasis) := by
  change coordinateSum (y - negativeThirdBasis) % 2 = 0
  rw [coordinateSum_sub, coordinateSum_negativeThirdBasis]
  have h := hy
  change coordinateSum y % 2 ≠ 0 at h
  omega

theorem discriminantMap_eq_one_of_integer_normal_form
    (x : dualSubgroup) (y : Ambient)
    (hy : ∀ i, x.1 i = (y i : ℚ)) :
    discriminantMap x = discriminantRepresentatives 0 ∨
    discriminantMap x = discriminantRepresentatives 1 := by
  by_cases hD : IsD4 y
  · left
    have hx : x =
        (⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩ : dualSubgroup) := by
      apply Subtype.ext
      funext i
      exact hy i
    have hm :
        (⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩ : dualSubgroup) ∈
          integralSubgroup := by
      exact (integerEmbedding_mem_integralSubgroup_iff y
        (integerEmbedding_mem_dual_ambient y)).2 hD
    have hz : discriminantMap
        (⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩ : dualSubgroup) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hm
    simpa [discriminantRepresentatives, hx] using hz
  · right
    let y' : Ambient := y - basisVector 0
    have hy' : IsD4 y' := d4_dual_adjusted_integer_mem y hD
    have hz :
        (⟨integerEmbedding y', integerEmbedding_mem_dual_ambient y'⟩ : dualSubgroup) ∈
          integralSubgroup := by
      exact (integerEmbedding_mem_integralSubgroup_iff y'
        (integerEmbedding_mem_dual_ambient y')).2 hy'
    have hdiff : x - firstCoordinateSubgroup =
        (⟨integerEmbedding y', integerEmbedding_mem_dual_ambient y'⟩ : dualSubgroup) := by
      apply Subtype.ext
      funext i
      have he : integerEmbedding y = x.1 := by
        funext j
        exact (hy j).symm
      change x.1 i - firstCoordinate i = integerEmbedding y' i
      rw [← he]
      change integerEmbedding y i - firstCoordinate i = integerEmbedding (y - basisVector 0) i
      simpa [integerEmbedding_sub_basisVector_zero] using congrFun
        (integerEmbedding_sub_basisVector_zero y) i
    have hq : discriminantMap x = discriminantMap firstCoordinateSubgroup := by
      apply discriminantMap_eq_of_sub_mem
      rw [hdiff]
      exact hz
    simpa [discriminantRepresentatives] using hq

theorem discriminantMap_eq_half_or_signedHalf_of_half_normal_form
    (x : dualSubgroup) (y : Ambient)
    (hy : ∀ i, x.1 i = (1 / 2 : ℚ) + (y i : ℚ)) :
    discriminantMap x = discriminantRepresentatives 2 ∨
    discriminantMap x = discriminantRepresentatives 3 := by
  by_cases hD : IsD4 y
  · left
    have hx : x = halfCoordinateSubgroup +
        (⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩ : dualSubgroup) := by
      apply Subtype.ext
      funext i
      exact hy i
    have hm :
        (⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩ : dualSubgroup) ∈
          integralSubgroup := by
      exact (integerEmbedding_mem_integralSubgroup_iff y
        (integerEmbedding_mem_dual_ambient y)).2 hD
    have hq : discriminantMap x = discriminantMap halfCoordinateSubgroup := by
      rw [hx, map_add]
      have hz : discriminantMap
          (⟨integerEmbedding y, integerEmbedding_mem_dual_ambient y⟩ : dualSubgroup) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).2 hm
      simp [hz]
    simpa [discriminantRepresentatives] using hq
  · right
    let y' : Ambient := y - negativeThirdBasis
    have hy' : IsD4 y' := d4_dual_adjusted_half_mem y hD
    have hz :
        (⟨integerEmbedding y', integerEmbedding_mem_dual_ambient y'⟩ : dualSubgroup) ∈
          integralSubgroup := by
      exact (integerEmbedding_mem_integralSubgroup_iff y'
        (integerEmbedding_mem_dual_ambient y')).2 hy'
    have hdiff : x - signedHalfCoordinateSubgroup =
        (⟨integerEmbedding y', integerEmbedding_mem_dual_ambient y'⟩ : dualSubgroup) := by
      apply Subtype.ext
      change x.1 - signedHalfCoordinate = integerEmbedding y'
      have he : x.1 - halfCoordinate = integerEmbedding y := by
        funext j
        change x.1 j - (1 / 2 : ℚ) = (y j : ℚ)
        linarith [hy j]
      have hs : signedHalfCoordinate = halfCoordinate +
          integerEmbedding negativeThirdBasis := by
        calc
          signedHalfCoordinate =
              (signedHalfCoordinate - halfCoordinate) + halfCoordinate := by abel
          _ = integerEmbedding negativeThirdBasis + halfCoordinate := by
            rw [signedHalf_sub_half_eq_integerEmbedding]
          _ = halfCoordinate + integerEmbedding negativeThirdBasis := by abel
      calc
        x.1 - signedHalfCoordinate =
            (x.1 - halfCoordinate) - integerEmbedding negativeThirdBasis := by
              rw [hs]
              ext j
              simp only [Pi.sub_apply, Pi.add_apply]
              ring
        _ = integerEmbedding y - integerEmbedding negativeThirdBasis := by rw [he]
        _ = integerEmbedding y' := by
          funext j
          change (y j : ℚ) - (negativeThirdBasis j : ℚ) =
            ((y j - negativeThirdBasis j : ℤ) : ℚ)
          norm_num
    have hq : discriminantMap x = discriminantMap signedHalfCoordinateSubgroup := by
      apply discriminantMap_eq_of_sub_mem
      rw [hdiff]
      exact hz
    simpa [discriminantRepresentatives] using hq

theorem discriminantMap_eq_one_of_four_representatives (x : dualSubgroup) :
    ∃ i : Fin 4, discriminantMap x = discriminantRepresentatives i := by
  let xd : DualLattice := ⟨x.1, x.2⟩
  rcases dual_integer_or_half_integer_normal_form xd with ⟨y, hy⟩ | ⟨y, hy⟩
  · rcases discriminantMap_eq_one_of_integer_normal_form x y hy with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rcases discriminantMap_eq_half_or_signedHalf_of_half_normal_form x y hy with h | h
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

end InfoGeometry.RootSystem.D4
