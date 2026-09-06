import Mathlib
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Projection rank over a real finite stage

This is the exact algebraic notion needed before a dimension-group/K-theory
bridge: the rank of an idempotent is the dimension of its linear range.
The tensor-stage doubling theorem is intentionally not asserted here; it
requires an explicit equivalence between the two relevant ranges.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.Cl11TensorTower

noncomputable def projectionRank {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) : ℕ :=
  Module.finrank K (LinearMap.range p)

theorem projectionRank_eq_finrank_range {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) :
    projectionRank p = Module.finrank K (LinearMap.range p) := rfl

theorem projectionRank_id {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    projectionRank (LinearMap.id : V →ₗ[K] V) = Module.finrank K V := by
  rw [projectionRank, LinearMap.range_id, finrank_top]

theorem projectionRank_zero {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] :
    projectionRank (0 : V →ₗ[K] V) = 0 := by
  rw [projectionRank, LinearMap.range_zero, finrank_bot]

abbrev IdempotentProjection (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] :=
  {p : V →ₗ[K] V // p.comp p = p}

namespace IdempotentProjection

abbrev map {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (p : IdempotentProjection K V) : V →ₗ[K] V :=
  p.1

abbrev idempotent {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (p : IdempotentProjection K V) : p.map.comp p.map = p.map :=
  p.2

end IdempotentProjection

noncomputable def IdempotentProjection.rank {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (p : IdempotentProjection K V) : ℕ :=
  projectionRank p.map

theorem IdempotentProjection.rank_eq_finrank_range
    {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (p : IdempotentProjection K V) :
    p.rank = Module.finrank K (LinearMap.range p.map) := rfl

abbrev RealStageProjection (n : ℕ) :=
  IdempotentProjection ℝ (MatStage n)

def realStageIdentityProjection (n : ℕ) : RealStageProjection n :=
  ⟨LinearMap.id, by simp⟩

def realStageZeroProjection (n : ℕ) : RealStageProjection n :=
  ⟨0, by simp⟩

theorem realStageIdentityProjection_rank (n : ℕ) :
    (realStageIdentityProjection n).rank =
      Module.finrank ℝ (MatStage n) := by
  exact projectionRank_id

theorem realStageZeroProjection_rank (n : ℕ) :
    (realStageZeroProjection n).rank = 0 := by
  exact projectionRank_zero

end InfoGeometry.Canonical
