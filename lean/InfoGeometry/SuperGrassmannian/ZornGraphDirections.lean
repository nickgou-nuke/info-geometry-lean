/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.ZornGraphChart
import InfoGeometry.SuperGrassmannian.GraphIdempotentDirections
import InfoGeometry.Algebra.ZornColorOperatorClosure
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Transport of graph and complement directions to native Zorn operators

The 32-dimensional idempotent direction space is not identified with the
16-dimensional fixed-complement graph parameter space. The native color odd
operators belong to the former; their two blocks can be read separately.
-/
noncomputable section
namespace InfoGeometry.SuperGrassmannian.ZornGraphChart
open InfoGeometry.Algebra ProjectorGraphChart GraphIdempotentDirections
variable {R : Type*} [CommRing R]

/-- Conjugation by the explicit splitting identifies the actual projector. -/
theorem conjugate_left_E11 :
    splitEquiv.conj (L_map (R := R) (ZornVectorMatrix.E11 : ZornVectorMatrix R)) =
      graphProjector (0 : Positive R →ₗ[R] Negative R) := by
  apply LinearMap.ext
  intro z
  change splitEquiv (L_map (R := R) ZornVectorMatrix.E11 (splitEquiv.symm z)) = _
  rw [splitEquiv_left_E11, splitEquiv.apply_symm_apply]

/-- The native first-order idempotent direction submodule in End(Zorn). -/
abbrev nativeIdempotentDirections : Submodule R (Module.End R (ZornVectorMatrix R)) :=
  (idempotentDirections (R := R) (M := Positive R) (N := Negative R)).comap
    splitEquiv.conj.toLinearMap

/-- Membership is exactly the corrected projector tangent equation. -/
theorem mem_nativeIdempotentDirections (T : Module.End R (ZornVectorMatrix R)) :
    T ∈ nativeIdempotentDirections ↔
      L_map (R := R) ZornVectorMatrix.E11 * T + T * L_map (R := R) ZornVectorMatrix.E11 = T := by
  change graphProjector 0 * splitEquiv.conj T + splitEquiv.conj T * graphProjector 0 =
    splitEquiv.conj T ↔ _
  rw [← conjugate_left_E11]
  have hm (A B : Module.End R (ZornVectorMatrix R)) :
      splitEquiv.conj (A * B) = splitEquiv.conj A * splitEquiv.conj B :=
    splitEquiv.conj_comp B A
  rw [← hm, ← hm, ← map_add, splitEquiv.conj.injective.eq_iff]

/-- Both independently varying corners, transported back to the actual octonion module. -/
def nativeDirectionsEquiv :
    ((Positive R →ₗ[R] Negative R) × (Negative R →ₗ[R] Positive R)) ≃ₗ[R]
      nativeIdempotentDirections (R := R) :=
  (idempotentDirectionsEquiv (R := R) (M := Positive R) (N := Negative R)).trans
    ((splitEquiv (R := R)).conj.ofSubmodule'
      (idempotentDirections (R := R) (M := Positive R) (N := Negative R))).symm

/-- The previously verified CAR odd space embeds in the idempotent directions. -/
theorem colorOdd_mem_nativeDirections {T : Module.End R (ZornVectorMatrix R)}
    (h : T ∈ ZornColorOperatorCoordinates.oddPart) : T ∈ nativeIdempotentDirections :=
  (mem_nativeIdempotentDirections T).mpr (ZornColorOperatorCoordinates.oddPart_tangent h)

/-- Actual graph projectors on Zorn, rather than only coordinate-product projectors. -/
def nativeGraphProjector (f : Positive R →ₗ[R] Negative R) :
    Module.End R (ZornVectorMatrix R) := splitEquiv.symm.conj (graphProjector f)

@[simp] theorem nativeGraphProjector_apply (f : Positive R →ₗ[R] Negative R)
    (X : ZornVectorMatrix R) :
    nativeGraphProjector f X = splitEquiv.symm ((X.a, X.v), f (X.a, X.v)) := rfl

theorem nativeGraphProjector_idempotent (f : Positive R →ₗ[R] Negative R) :
    IsIdempotentElem (nativeGraphProjector f) := by
  apply LinearMap.ext
  intro X
  simp [Module.End.mul_apply]

@[simp] theorem nativeGraphProjector_zero :
    nativeGraphProjector (0 : Positive R →ₗ[R] Negative R) =
      L_map (R := R) (ZornVectorMatrix.E11 : ZornVectorMatrix R) := by
  apply LinearMap.ext
  intro X
  rw [nativeGraphProjector_apply, ZornVectorMatrix.left_E11_apply]
  rfl

/-- Its range is the submodule of the native Grassmannian chart point. -/
theorem range_nativeGraphProjector (f : Positive R →ₗ[R] Negative R) :
    LinearMap.range (nativeGraphProjector f) = LinearMap.ker (graphReadout f) := by
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    rw [mem_graphKernel]
    rfl
  · intro h
    refine ⟨X, ?_⟩
    have hm := (mem_graphKernel f X).mp h
    rw [nativeGraphProjector_apply, ← hm]
    rfl

/-- Only one of the two corners appears in fixed-complement graph variation. -/
theorem nativeGraphProjector_difference (f : Positive R →ₗ[R] Negative R) :
    nativeGraphProjector f - nativeGraphProjector 0 =
      splitEquiv.symm.conj (offDiagonalMap (f, (0 : Negative R →ₗ[R] Positive R))) := by
  unfold nativeGraphProjector
  rw [← map_sub, graphProjector_difference]

/-- The actual image-moving graph coordinate of a general CAR odd operator. -/
theorem color_lowerBlock_apply (p q u : ZornVec3 R) (a : R) :
    lowerBlock (splitEquiv.conj (ZornColorOperatorCoordinates.oddMap (p, q))) (a, u) =
      (-a • q + ZornVec3.cross p u, -ZornVec3.dot q u) := by
  ext i
  all_goals try fin_cases i
  all_goals simp [lowerBlock, LinearEquiv.conj_apply_apply, splitEquiv_apply,
    splitEquiv_symm_apply, ZornColorOperatorCoordinates.oddMap_apply,
    ZornVectorMatrix.mul, ZornVectorMatrix.offDiagonal,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-- The distinct complement-moving coordinate of the same CAR odd operator. -/
theorem color_upperBlock_apply (p q v : ZornVec3 R) (b : R) :
    upperBlock (splitEquiv.conj (ZornColorOperatorCoordinates.oddMap (p, q))) (v, b) =
      (ZornVec3.dot p v, b • p + ZornVec3.cross q v) := by
  ext i
  all_goals try fin_cases i
  all_goals simp [upperBlock, LinearEquiv.conj_apply_apply, splitEquiv_apply,
    splitEquiv_symm_apply, ZornColorOperatorCoordinates.oddMap_apply,
    ZornVectorMatrix.mul, ZornVectorMatrix.offDiagonal,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  all_goals ring

/-- A single color generator has both blocks nonzero: it is not solely a graph direction. -/
theorem color_generator_both_blocks_nonzero [Nontrivial R] :
    let T := splitEquiv.conj
      (ZornColorOperatorCoordinates.oddMap (ZornVec3.basis (R := R) 0, 0))
    lowerBlock T ≠ 0 ∧ upperBlock T ≠ 0 := by
  dsimp only
  constructor
  · intro h
    have ht := congrArg (fun f : Positive R →ₗ[R] Negative R =>
      (f (0, ZornVec3.basis 1)).1 2) h
    simp [color_lowerBlock_apply, ZornVec3.basis] at ht
  · intro h
    have ht := congrArg (fun g : Negative R →ₗ[R] Positive R => (g (0, 1)).2 0) h
    simp [color_upperBlock_apply, ZornVec3.basis] at ht

section Dimension
variable {K : Type*} [Field K]

/-- Dimension of the image-moving graph parameters. -/
theorem finrank_graph_parameters :
    Module.finrank K (Positive K →ₗ[K] Negative K) = 16 := by
  simp [Module.finrank_linearMap, Positive, Negative, ZornVec3, Module.finrank_prod]

/-- Allowing independent complement motion doubles the parameter dimension. -/
theorem finrank_nativeIdempotentDirections :
    Module.finrank K (nativeIdempotentDirections (R := K)) = 32 := by
  have h := (nativeDirectionsEquiv (R := K)).finrank_eq
  apply h.symm.trans
  simp [Module.finrank_prod, Module.finrank_linearMap, Positive, Negative, ZornVec3]

end Dimension
end InfoGeometry.SuperGrassmannian.ZornGraphChart
