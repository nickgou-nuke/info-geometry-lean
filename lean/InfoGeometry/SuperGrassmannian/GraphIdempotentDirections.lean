/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.ProjectorGraphChart
import InfoGeometry.Core.PeirceTangent

/-! # Graph directions versus idempotent directions

At the standard first-summand projector, the algebraic idempotent tangent
space is Hom(M,N) × Hom(N,M). Only the first factor changes the graph when
the complement is fixed. The second factor changes the complementary kernel
while preserving the image. These are exact algebraic statements; no analytic
derivative or supermanifold is asserted.
-/
namespace InfoGeometry.SuperGrassmannian.GraphIdempotentDirections
open ProjectorGraphChart
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Both directed off-diagonal corners as actual endomorphisms. -/
def offDiagonalMap : ((M →ₗ[R] N) × (N →ₗ[R] M)) →ₗ[R] Module.End R (M × N) where
  toFun t := (t.2.comp (LinearMap.snd R M N)).prod (t.1.comp (LinearMap.fst R M N))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem offDiagonalMap_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M) (z : M × N) :
    offDiagonalMap (f, g) z = (g z.2, f z.1) := rfl

/-- Read the image-moving corner. -/
def lowerBlock (T : Module.End R (M × N)) : M →ₗ[R] N :=
  (LinearMap.snd R M N).comp (T.comp (LinearMap.inl R M N))

/-- Read the complement-moving corner. -/
def upperBlock (T : Module.End R (M × N)) : N →ₗ[R] M :=
  (LinearMap.fst R M N).comp (T.comp (LinearMap.inr R M N))

/-- Native submodule of solutions to the first-order idempotent equation. -/
def idempotentDirections : Submodule R (Module.End R (M × N)) where
  carrier := {T | graphProjector (0 : M →ₗ[R] N) * T + T * graphProjector 0 = T}
  zero_mem' := by simp
  add_mem' := by
    intro T U ht hu
    calc
      _ = (graphProjector 0 * T + T * graphProjector 0) +
          (graphProjector 0 * U + U * graphProjector 0) := by noncomm_ring
      _ = _ := by rw [ht, hu]
  smul_mem' := by
    intro c T ht
    calc
      _ = c • (graphProjector 0 * T + T * graphProjector 0) := by
        simp [smul_add]
      _ = _ := by rw [ht]

theorem offDiagonalMap_mem (t : (M →ₗ[R] N) × (N →ₗ[R] M)) :
    offDiagonalMap t ∈ idempotentDirections := by
  rcases t with ⟨f, g⟩
  apply LinearMap.ext
  intro z
  simp [Module.End.mul_apply, graphProjector_apply]

/-- Extracting both corners is precisely the off-diagonal Peirce projection. -/
theorem offDiagonalMap_blocks (T : Module.End R (M × N)) :
    offDiagonalMap (lowerBlock T, upperBlock T) =
      graphProjector (0 : M →ₗ[R] N) * T * (1 - graphProjector 0) +
        (1 - graphProjector 0) * T * graphProjector 0 := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, graphProjector_apply, LinearMap.zero_apply, offDiagonalMap_apply]
  have hz : z - (z.1, (0 : N)) = (0, z.2) := by ext <;> simp
  rw [hz]
  ext <;> simp [lowerBlock, upperBlock]

/-- Every idempotent direction has exactly these two blocks, in every characteristic. -/
def idempotentDirectionsEquiv :
    ((M →ₗ[R] N) × (N →ₗ[R] M)) ≃ₗ[R] idempotentDirections (R := R) (M := M) (N := N) where
  toFun t := ⟨offDiagonalMap t, offDiagonalMap_mem t⟩
  invFun T := (lowerBlock T.1, upperBlock T.1)
  left_inv t := rfl
  right_inv T := by
    apply Subtype.ext
    change offDiagonalMap (lowerBlock T.1, upperBlock T.1) = T.1
    rw [offDiagonalMap_blocks]
    exact (InfoGeometry.Core.PeirceTangent.tangent_eq_offDiagonal
      (graphProjector_mul 0 0) T.2).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The graph-projector family is affine with only the image-moving block. -/
theorem graphProjector_difference (f : M →ₗ[R] N) :
    graphProjector f - graphProjector 0 = offDiagonalMap (f, (0 : N →ₗ[R] M)) := by
  apply LinearMap.ext
  intro z
  simp [graphProjector_apply]

/-- Vary the complement while keeping the image fixed. -/
def complementProjector (g : N →ₗ[R] M) : Module.End R (M × N) :=
  graphProjector (0 : M →ₗ[R] N) + offDiagonalMap (0, g)

@[simp] theorem complementProjector_apply (g : N →ₗ[R] M) (z : M × N) :
    complementProjector g z = (z.1 + g z.2, 0) := by
  simp [complementProjector, graphProjector_apply]

theorem complementProjector_idempotent (g : N →ₗ[R] M) :
    IsIdempotentElem (complementProjector g) := by
  apply LinearMap.ext
  intro z
  simp [Module.End.mul_apply]

/-- These directions genuinely retain the same submodule, despite changing projectors. -/
theorem range_complementProjector (g : N →ₗ[R] M) :
    LinearMap.range (complementProjector g) =
      LinearMap.range (graphProjector (0 : M →ₗ[R] N)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(w.1 + g w.2, 0), by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(w.1, 0), by simp⟩

theorem complementProjector_injective :
    Function.Injective (complementProjector (R := R) (M := M) (N := N)) := by
  intro g h he
  apply LinearMap.ext
  intro y
  have hy := congrArg Prod.fst (LinearMap.congr_fun he (0, y))
  simpa using hy

end InfoGeometry.SuperGrassmannian.GraphIdempotentDirections
