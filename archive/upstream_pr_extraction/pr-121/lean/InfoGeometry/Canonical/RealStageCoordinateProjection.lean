import Mathlib
import InfoGeometry.Canonical.RealUHFProjectionRankTailTransport

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.TowerMatrix

/-!
# Rank-one coordinate projections on finite real stages

This owner supplies the first non-endpoint finite-stage seed for the tail
construction.  It uses the native function-space carrier and no matrix-rank
or `K₀` classification claim.
-/

noncomputable def coordinateProjection {ι : Type*} [DecidableEq ι]
    (i : ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  { toFun := fun x j => if j = i then x i else 0
    map_add' := by
      intro x y
      funext j
      by_cases h : j = i <;> simp [h]
    map_smul' := by
      intro c x
      funext j
      by_cases h : j = i <;> simp [h] }

@[simp] theorem coordinateProjection_apply {ι : Type*} [DecidableEq ι]
    (i j : ι) (x : ι → ℝ) :
    coordinateProjection i x j = if j = i then x i else 0 := by
  rfl

theorem coordinateProjection_idempotent {ι : Type*} [DecidableEq ι]
    (i : ι) :
    (coordinateProjection i).comp (coordinateProjection i) =
      coordinateProjection i := by
  apply LinearMap.ext
  intro x
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateProjection_apply]
  · simp [coordinateProjection_apply, h]

noncomputable def coordinateRangeEquiv {ι : Type*} [DecidableEq ι]
    [Fintype ι] (i : ι) :
    LinearMap.range (coordinateProjection i) ≃ₗ[ℝ] ℝ where
  toFun x := x.1 i
  invFun c :=
    ⟨Pi.single i c, ⟨Pi.single i c, by
      apply funext
      intro j
      by_cases h : j = i
      · subst j
        simp [coordinateProjection_apply]
      · simp [coordinateProjection_apply, h]⟩⟩
  left_inv x := by
    rcases x.property with ⟨y, hy⟩
    apply Subtype.ext
    apply funext
    intro j
    by_cases h : j = i
    · subst j
      simp
    · have hj := congrFun hy j
      simp [coordinateProjection_apply, h] at hj
      simpa [Pi.single_apply, h] using hj
  right_inv c := by
    simp
  map_add' x y := by
    rfl
  map_smul' c x := by
    rfl

theorem coordinateProjection_rank {ι : Type*} [DecidableEq ι]
    [Fintype ι] (i : ι) :
    projectionRank (coordinateProjection i) = 1 := by
  change Module.finrank ℝ (LinearMap.range (coordinateProjection i)) = 1
  rw [(coordinateRangeEquiv i).finrank_eq]
  simp

noncomputable def coordinateIdempotentProjection {ι : Type*}
    [DecidableEq ι] [Fintype ι] (i : ι) :
    IdempotentProjection ℝ (ι → ℝ) :=
  ⟨coordinateProjection i, coordinateProjection_idempotent i⟩

noncomputable def realStageCoordinateProjection (n : ℕ) (i : Idx n) :
    IdempotentProjection ℝ (RealStageVector n) :=
  coordinateIdempotentProjection i

theorem realStageCoordinateProjection_rank (n : ℕ) (i : Idx n) :
    projectionRank (realStageCoordinateProjection n i).map = 1 := by
  simpa [realStageCoordinateProjection] using coordinateProjection_rank i

noncomputable def halfTailSystem :
    RealUHFProjectionRankTailSystem 1 :=
  transportedTailSystem 1 (realStageCoordinateProjection 1 default)

theorem halfTailSystem_readout_zero :
    (halfTailSystem.normalizedReadout 0 : ℚ) = 1 / 2 := by
  change normalizedProjectionRank
      (realStageCoordinateProjection 1 default) = 1 / 2
  unfold normalizedProjectionRank
  rw [realStageCoordinateProjection_rank]
  norm_num

theorem halfTailSystem_readout (n : ℕ) :
    (halfTailSystem.normalizedReadout n : ℚ) = 1 / 2 := by
  have hstable :=
    RealUHFProjectionRankTailSystem.normalizedReadout_add
      halfTailSystem 0 n
  have hstableQ := congrArg
    (fun q : DyadicRational => (q : ℚ)) hstable
  have hstableQ' :
      (halfTailSystem.normalizedReadout n : ℚ) =
        (halfTailSystem.normalizedReadout 0 : ℚ) := by
    simpa [RealUHFProjectionRankTailIndex.add] using hstableQ
  rw [hstableQ']
  exact halfTailSystem_readout_zero

end InfoGeometry.Canonical
