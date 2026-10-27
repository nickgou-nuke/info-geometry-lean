/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.ProjectionIncidence
import InfoGeometry.Projective.ProjectionNoncommutativity
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Full matrix realization of projective incidence operators

The native star-algebra equivalence `LinearMap.toMatrixOrthonormal` represents
all operators, in an arbitrary orthonormal basis. Incidence, intersection and
genuine noncommutativity are transported without a diagonal restriction.
-/

noncomputable section

namespace InfoGeometry.Projective.ProjectionMatrixGeometry

open ProjectionIncidence

variable {E n : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype n] [DecidableEq n]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Apply mathlib's full star-algebra matrix equivalence to a continuous operator. -/
def operatorMatrix (b : OrthonormalBasis n ℂ E) (T : E →L[ℂ] E) : Matrix n n ℂ :=
  LinearMap.toMatrixOrthonormal b T.toLinearMap

variable (b : OrthonormalBasis n ℂ E)

theorem operatorMatrix_injective : Function.Injective (operatorMatrix b) := by
  intro S T h
  exact ContinuousLinearMap.coe_injective ((LinearMap.toMatrixOrthonormal b).injective h)

/-- Every matrix is represented; the carrier is the full matrix algebra. -/
theorem operatorMatrix_surjective : Function.Surjective (operatorMatrix b) := by
  intro A
  refine ⟨((LinearMap.toMatrixOrthonormal b).symm A).toContinuousLinearMap, ?_⟩
  change (LinearMap.toMatrixOrthonormal b) ((LinearMap.toMatrixOrthonormal b).symm A) = A
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply A

@[simp] theorem operatorMatrix_mul (S T : E →L[ℂ] E) :
    operatorMatrix b (S * T) = operatorMatrix b S * operatorMatrix b T :=
  map_mul (LinearMap.toMatrixOrthonormal b) S.toLinearMap T.toLinearMap

theorem operatorMatrix_commute_iff (S T : E →L[ℂ] E) :
    Commute (operatorMatrix b S) (operatorMatrix b T) ↔ Commute S T := by
  change operatorMatrix b S * operatorMatrix b T = operatorMatrix b T * operatorMatrix b S
    ↔ S * T = T * S
  rw [← operatorMatrix_mul, ← operatorMatrix_mul]
  exact (operatorMatrix_injective b).eq_iff

/-- Matrix rank is the dimension of the operator range, not the span of its entries. -/
theorem operatorMatrix_rank (T : E →L[ℂ] E) :
    (operatorMatrix b T).rank = Module.finrank ℂ T.range := by
  change (LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap).rank = _
  rw [Matrix.rank_eq_finrank_range_toLin _ b.toBasis b.toBasis, Matrix.toLin_toMatrix]

theorem operatorMatrix_isStarProjection {T : E →L[ℂ] E} (hT : IsStarProjection T) :
    IsStarProjection (operatorMatrix b T) := by
  have hlin : IsStarProjection T.toLinearMap :=
    ⟨hT.isIdempotentElem.toLinearMap,
      (T.isSelfAdjoint_toLinearMap_iff).mpr hT.isSelfAdjoint⟩
  exact hlin.map (LinearMap.toMatrixOrthonormal b)

/-- Matrix of the canonical orthogonal projector onto an arbitrary subspace. -/
def subspaceMatrix (U : Submodule ℂ E) : Matrix n n ℂ :=
  operatorMatrix b U.starProjection

/-- Matrix of the canonical rank-one projector associated with a projective point. -/
def pointMatrix (p : Projectivization ℂ E) : Matrix n n ℂ :=
  operatorMatrix b (pointProjection p)

theorem pointMatrix_isStarProjection (p : Projectivization ℂ E) :
    IsStarProjection (pointMatrix b p) :=
  operatorMatrix_isStarProjection b (pointProjection_isStarProjection p)

@[simp] theorem pointMatrix_rank (p : Projectivization ℂ E) :
    (pointMatrix b p).rank = 1 := by
  exact (operatorMatrix_rank b (pointProjection p)).trans (pointProjection_rank p)

theorem pointMatrix_injective : Function.Injective (pointMatrix b) :=
  (operatorMatrix_injective b).comp pointProjection_injective

/-- Geometric incidence is ordinary, order-sensitive matrix multiplication. -/
theorem le_iff_subspaceMatrix_mul (U W : Submodule ℂ E) :
    U ≤ W ↔ subspaceMatrix b W * subspaceMatrix b U = subspaceMatrix b U := by
  rw [le_iff_projection_mul U W]
  change W.starProjection * U.starProjection = U.starProjection ↔
    operatorMatrix b W.starProjection * operatorMatrix b U.starProjection =
      operatorMatrix b U.starProjection
  rw [← operatorMatrix_mul]
  exact (operatorMatrix_injective b).eq_iff.symm

theorem point_incident_iff_matrix_mul (p : Projectivization ℂ E) (W : Submodule ℂ E) :
    p.submodule ≤ W ↔ subspaceMatrix b W * pointMatrix b p = pointMatrix b p :=
  le_iff_subspaceMatrix_mul b p.submodule W

/-- The matrix product equals the geometric meet precisely in the commuting case. -/
theorem matrix_mul_eq_inf_iff (U W : Submodule ℂ E) :
    subspaceMatrix b U * subspaceMatrix b W = subspaceMatrix b (U ⊓ W) ↔
      Commute (subspaceMatrix b U) (subspaceMatrix b W) := by
  change operatorMatrix b U.starProjection * operatorMatrix b W.starProjection =
      operatorMatrix b (U ⊓ W).starProjection ↔
    Commute (operatorMatrix b U.starProjection) (operatorMatrix b W.starProjection)
  rw [← operatorMatrix_mul, operatorMatrix_commute_iff,
    (operatorMatrix_injective b).eq_iff]
  exact mul_eq_inf_projection_iff U W

/-- In every dimension at least two, actual point projectors give noncommuting matrices
in every choice of orthonormal basis. -/
theorem exists_noncommuting_pointMatrices (hdim : 2 ≤ Module.finrank ℂ E) :
    ∃ p q : Projectivization ℂ E, p ≠ q ∧
      ¬ Commute (pointMatrix b p) (pointMatrix b q) := by
  obtain ⟨p, q, hpq, hcomm⟩ :=
    ProjectionNoncommutativity.exists_noncommuting_ray_projections hdim
  refine ⟨p, q, hpq, fun h => hcomm ?_⟩
  exact (operatorMatrix_commute_iff b (pointProjection p) (pointProjection q)).mp h

/-- A witness statement entirely inside the native full matrix algebra. -/
theorem exists_noncommuting_rankOne_matrices (hdim : 2 ≤ Module.finrank ℂ E) :
    ∃ A B : Matrix n n ℂ,
      IsStarProjection A ∧ IsStarProjection B ∧ A.rank = 1 ∧ B.rank = 1 ∧
        A ≠ B ∧ ¬ Commute A B := by
  obtain ⟨p, q, hpq, hcomm⟩ := exists_noncommuting_pointMatrices b hdim
  exact ⟨pointMatrix b p, pointMatrix b q,
    pointMatrix_isStarProjection b p, pointMatrix_isStarProjection b q,
    pointMatrix_rank b p, pointMatrix_rank b q,
    fun h => hpq (pointMatrix_injective b h), hcomm⟩

end InfoGeometry.Projective.ProjectionMatrixGeometry
