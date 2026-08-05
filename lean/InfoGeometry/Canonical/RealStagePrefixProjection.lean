import Mathlib
import InfoGeometry.Canonical.RealProjectionRankConjugation
import InfoGeometry.Canonical.RealUHFProjectionRankTailTransport

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.TowerMatrix

/-!
# Prefix projections of arbitrary finite rank

The prefix projection on `Fin N → ℝ` keeps the first `r` coordinates.  Its
range is linearly equivalent to `Fin r → ℝ`, so its rank is exactly `r`.
Conjugation by the native tensor-index equivalence then gives the same
construction on `RealStageVector n`.
-/

def prefixProjection (r N : ℕ) (hr : r ≤ N) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x i := if i.1 < r then x i else 0
  map_add' x y := by
    funext i
    by_cases h : i.1 < r <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.1 < r <;> simp [h]

@[simp] theorem prefixProjection_apply
    (r N : ℕ) (hr : r ≤ N) (x : Fin N → ℝ) (i : Fin N) :
    prefixProjection r N hr x i = if i.1 < r then x i else 0 := rfl

theorem prefixProjection_idempotent
    (r N : ℕ) (hr : r ≤ N) :
    (prefixProjection r N hr).comp (prefixProjection r N hr) =
      prefixProjection r N hr := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases h : i.1 < r <;> simp [prefixProjection_apply, h]

noncomputable def prefixRangeEquiv
    (r N : ℕ) (hr : r ≤ N) :
    LinearMap.range (prefixProjection r N hr) ≃ₗ[ℝ] (Fin r → ℝ) where
  toFun x := fun j => x.1 (Fin.castLE hr j)
  invFun f :=
    ⟨fun i => if h : i.1 < r then f ⟨i.1, h⟩ else 0, by
      refine ⟨fun i => if h : i.1 < r then f ⟨i.1, h⟩ else 0, ?_⟩
      apply funext
      intro i
      by_cases h : i.1 < r <;> simp [prefixProjection_apply, h]⟩
  left_inv x := by
    rcases x.property with ⟨y, hy⟩
    apply Subtype.ext
    funext i
    by_cases h : i.1 < r
    · have hi : Fin.castLE hr ⟨i.1, h⟩ = i := by
        apply Fin.ext
        rfl
      simp [hy, prefixProjection_apply, h, hi]
    · have hi := congrFun hy i
      simp [prefixProjection_apply, h] at hi
      simpa [h] using hi
  right_inv f := by
    funext j
    simp
  map_add' x y := by rfl
  map_smul' c x := by rfl

theorem prefixProjection_rank
    (r N : ℕ) (hr : r ≤ N) :
    projectionRank (prefixProjection r N hr) = r := by
  change Module.finrank ℝ (LinearMap.range (prefixProjection r N hr)) = r
  rw [(prefixRangeEquiv r N hr).finrank_eq]
  simp [Module.finrank_pi]

noncomputable def stageVectorFinEquiv (n : ℕ) :
    RealStageVector n ≃ₗ[ℝ] (Fin (2 ^ n) → ℝ) :=
  LinearEquiv.piCongrLeft ℝ (fun _ : Fin (2 ^ n) => ℝ)
    (idxEquivFinPowTwo n)

noncomputable def realStagePrefixProjection
    (n r : ℕ) (hr : r ≤ 2 ^ n) :
    RealStageVector n →ₗ[ℝ] RealStageVector n :=
  conjugateLinearMap (stageVectorFinEquiv n).symm
    (prefixProjection r (2 ^ n) hr)

theorem realStagePrefixProjection_idempotent
    (n r : ℕ) (hr : r ≤ 2 ^ n) :
    (realStagePrefixProjection n r hr).comp
        (realStagePrefixProjection n r hr) =
      realStagePrefixProjection n r hr := by
  let e := (stageVectorFinEquiv n).symm
  let p := prefixProjection r (2 ^ n) hr
  have hp : p.comp p = p := prefixProjection_idempotent r (2 ^ n) hr
  apply LinearMap.ext
  intro x
  change e (p (e.symm (e (p (e.symm x))))) = e (p (e.symm x))
  rw [e.symm_apply_apply]
  exact congrArg e (LinearMap.congr_fun hp (e.symm x))

noncomputable def realStagePrefixIdempotentProjection
    (n r : ℕ) (hr : r ≤ 2 ^ n) :
    IdempotentProjection ℝ (RealStageVector n) :=
  ⟨realStagePrefixProjection n r hr,
    realStagePrefixProjection_idempotent n r hr⟩

theorem realStagePrefixProjection_rank
    (n r : ℕ) (hr : r ≤ 2 ^ n) :
    projectionRank (realStagePrefixIdempotentProjection n r hr).map = r := by
  unfold realStagePrefixIdempotentProjection realStagePrefixProjection
  rw [projectionRank_conjugate]
  exact prefixProjection_rank r (2 ^ n) hr

noncomputable def prefixTailSystem
    (n r : ℕ) (hr : r ≤ 2 ^ n) :
    RealUHFProjectionRankTailSystem n :=
  transportedTailSystem n (realStagePrefixIdempotentProjection n r hr)

theorem prefixTailSystem_readout
    (n r : ℕ) (hr : r ≤ 2 ^ n) (k : ℕ) :
    (prefixTailSystem n r hr).normalizedReadout k =
      normalizedProjectionRankDyadic
        (realStagePrefixIdempotentProjection n r hr) := by
  exact transportedTailSystem_readout_add n
    (realStagePrefixIdempotentProjection n r hr) k

theorem prefixTailSystem_readout_value
    (n r : ℕ) (hr : r ≤ 2 ^ n) (k : ℕ) :
    ((prefixTailSystem n r hr).normalizedReadout k : ℚ) =
      (r : ℚ) / (2 : ℚ) ^ n := by
  rw [prefixTailSystem_readout]
  change normalizedProjectionRank
      (realStagePrefixIdempotentProjection n r hr) = _
  unfold normalizedProjectionRank
  rw [realStagePrefixProjection_rank]

end InfoGeometry.Canonical
