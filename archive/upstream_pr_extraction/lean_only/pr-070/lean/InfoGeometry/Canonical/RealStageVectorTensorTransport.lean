import Mathlib
import InfoGeometry.Canonical.RealProjectionRankDoubling

/-!
# Vector-level transport for the binary Clifford tower

The tensor index satisfies `Idx (n+1) = Idx n × Fin 2`.  This file makes the
corresponding two-copy decomposition of stage vectors explicit and transports
the product-double projection through it.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.TowerMatrix

abbrev RealStageVector (n : ℕ) := Idx n → ℝ

theorem realStageVector_finrank (n : ℕ) :
    Module.finrank ℝ (RealStageVector n) = 2 ^ n := by
  simp [RealStageVector, Module.finrank_pi, idx_card_pow_two]

theorem projectionRank_le_realStageVector
    {n : ℕ} (p : RealStageVector n →ₗ[ℝ] RealStageVector n) :
    projectionRank p ≤ 2 ^ n := by
  rw [← realStageVector_finrank n]
  exact LinearMap.finrank_range_le p

noncomputable def realStageVectorDouble (n : ℕ) :
    RealStageVector (n + 1) ≃ₗ[ℝ]
      (RealStageVector n × RealStageVector n) where
  toFun x :=
    (fun i => x (i, (0 : Fin 2)), fun i => x (i, (1 : Fin 2)))
  invFun x := fun ij =>
    match ij.2 with
    | 0 => x.1 ij.1
    | 1 => x.2 ij.1
  left_inv x := by
    funext ij
    cases ij with
    | mk i j => fin_cases j <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      rfl
    · funext i
      rfl
  map_add' x y := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' c x := by
    apply Prod.ext <;> funext i <;> rfl

@[simp] theorem realStageVectorDouble_left (n : ℕ)
    (x : RealStageVector (n + 1)) (i : Idx n) :
    (realStageVectorDouble n x).1 i = x (i, (0 : Fin 2)) := rfl

@[simp] theorem realStageVectorDouble_right (n : ℕ)
    (x : RealStageVector (n + 1)) (i : Idx n) :
    (realStageVectorDouble n x).2 i = x (i, (1 : Fin 2)) := rfl

noncomputable def transportedDoubleProjection {n : ℕ}
    (p : RealStageVector n →ₗ[ℝ] RealStageVector n) :
    RealStageVector (n + 1) →ₗ[ℝ] RealStageVector (n + 1) :=
  (realStageVectorDouble n).symm.toLinearMap.comp
    ((doubleProjection p).comp (realStageVectorDouble n).toLinearMap)

theorem transportedDoubleProjection_idempotent {n : ℕ}
    {p : RealStageVector n →ₗ[ℝ] RealStageVector n}
    (hp : p.comp p = p) :
    (transportedDoubleProjection p).comp
        (transportedDoubleProjection p) =
      transportedDoubleProjection p := by
  apply LinearMap.ext
  intro x
  have hpoint (y : RealStageVector n) : p (p y) = p y :=
    LinearMap.congr_fun hp y
  change
    (realStageVectorDouble n).symm
        ((doubleProjection p)
          ((realStageVectorDouble n)
            ((realStageVectorDouble n).symm
              ((doubleProjection p) ((realStageVectorDouble n) x))))) =
      (realStageVectorDouble n).symm
        ((doubleProjection p) ((realStageVectorDouble n) x))
  rw [(realStageVectorDouble n).apply_symm_apply]
  apply congrArg (realStageVectorDouble n).symm
  apply Prod.ext <;> exact hpoint _

end InfoGeometry.Canonical
