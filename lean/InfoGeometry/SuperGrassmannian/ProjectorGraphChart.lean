/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Projection

/-!
# Graph submodules and their noncommutative projectors

A graph chart chooses a fixed complement. Its endomorphism projector remembers
that complement as its kernel. This algebraic chart construction does not
assert a supermanifold atlas or a super-Grassmannian representability theorem.
-/

namespace InfoGeometry.SuperGrassmannian.ProjectorGraphChart

variable {R M N : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Projection onto the graph of `f` along the second summand. -/
def graphProjector (f : M →ₗ[R] N) : Module.End R (M × N) :=
  (LinearMap.fst R M N).prod (f.comp (LinearMap.fst R M N))

@[simp] theorem graphProjector_apply (f : M →ₗ[R] N) (z : M × N) :
    graphProjector f z = (z.1, f z.1) := rfl

/-- Composition retains the left projector, so this family is generally
noncommutative. -/
@[simp] theorem graphProjector_mul (f g : M →ₗ[R] N) :
    graphProjector f * graphProjector g = graphProjector f := by
  ext z <;> rfl

theorem graphProjector_idempotent (f : M →ₗ[R] N) :
    IsIdempotentElem (graphProjector f) := graphProjector_mul f f

@[simp] theorem range_graphProjector (f : M →ₗ[R] N) :
    LinearMap.range (graphProjector f) = f.graph := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hz
    exact ⟨z, Prod.ext rfl hz.symm⟩

@[simp] theorem ker_graphProjector (f : M →ₗ[R] N) :
    LinearMap.ker (graphProjector f) = LinearMap.ker (LinearMap.fst R M N) := by
  ext z
  simp only [LinearMap.mem_ker, graphProjector_apply, LinearMap.fst_apply,
    Prod.mk_eq_zero]
  exact ⟨And.left, fun h => ⟨h, by rw [h, map_zero]⟩⟩

theorem graphProjector_injective :
    Function.Injective (graphProjector (R := R) (M := M) (N := N)) := by
  intro f g h
  ext x
  exact congrArg Prod.snd (LinearMap.congr_fun h (x, 0))

/-- Distinct graph coordinates yield genuinely noncommuting projectors. -/
theorem graphProjector_commute_iff (f g : M →ₗ[R] N) :
    Commute (graphProjector f) (graphProjector g) ↔ f = g := by
  change graphProjector f * graphProjector g = graphProjector g * graphProjector f ↔ _
  rw [graphProjector_mul, graphProjector_mul]
  exact graphProjector_injective.eq_iff

/-- All complementary projectors have the same image, the second summand.
Thus their image alone does not retain the choice of complement. -/
theorem range_complement_graphProjector (f : M →ₗ[R] N) :
    LinearMap.range (1 - graphProjector f) =
      LinearMap.ker (LinearMap.fst R M N) := by
  rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub (graphProjector_idempotent f),
    ker_graphProjector]

/-- Despite their common image, distinct graph parameters give distinct
complementary projectors. -/
theorem complement_graphProjector_eq_iff (f g : M →ₗ[R] N) :
    1 - graphProjector f = 1 - graphProjector g ↔ f = g := by
  rw [sub_right_inj]
  exact graphProjector_injective.eq_iff

/-- The graph projector commutes with a block endomorphism exactly when its
coordinate map intertwines the two blocks. For involutive blocks this is the
precise grading-preservation condition; no involutivity is needed here. -/
theorem graphProjector_commute_prodMap_iff
    (f : M →ₗ[R] N) (KM : Module.End R M) (KN : Module.End R N) :
    Commute (graphProjector f) (KM.prodMap KN) ↔ f.comp KM = KN.comp f := by
  constructor
  · intro h
    ext x
    exact congrArg Prod.snd (LinearMap.congr_fun h.eq (x, 0))
  · intro h
    change graphProjector f * KM.prodMap KN = KM.prodMap KN * graphProjector f
    apply LinearMap.ext
    intro z
    exact Prod.ext rfl (LinearMap.congr_fun h z.1)

end InfoGeometry.SuperGrassmannian.ProjectorGraphChart
