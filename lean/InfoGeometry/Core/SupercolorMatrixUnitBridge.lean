/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorMatrixExamples

/-!
# Faithful color-corner embedding and noncommutative finite witnesses

The `Option ι` common-source and `ι × Bool` disjoint-sector matrix units are
reused from `SupercolorMatrixExamples`. The former carries off-diagonal color
mixing; the latter realizes the supplied two/four-color orthogonal examples.
The native nonunital ring hom below is an ordinary color-algebra embedding,
not a claimed `sl(k|1)` representation or a common-Hamiltonian SUSY algebra.
-/

namespace InfoGeometry.Core.SupercolorMatrixUnitBridge

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.Core.SupercolorMatrixExamples

section ColorEmbedding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [Ring R]

/-- Extend a color matrix by zero on the distinguished source coordinate. -/
def colorEmbedding (M : Matrix ι ι R) : Matrix (Option ι) (Option ι) R
  | some i, some j => M i j
  | _, _ => 0

/-- Multiplicative additive embedding into the color corner. It is deliberately
nonunital in the full ambient matrix ring. -/
def colorEmbeddingHom : Matrix ι ι R →ₙ+* Matrix (Option ι) (Option ι) R where
  toFun := colorEmbedding
  map_zero' := by
    ext i j
    cases i <;> cases j <;> rfl
  map_add' M N := by
    ext i j
    cases i <;> cases j <;> simp [colorEmbedding]
  map_mul' M N := by
    ext i j
    cases i <;> cases j <;>
      simp [colorEmbedding, Matrix.mul_apply, Fintype.sum_option]

omit [DecidableEq ι] in
theorem colorEmbedding_injective :
    Function.Injective (colorEmbeddingHom (ι := ι) (R := R)) := by
  intro M N h
  ext i j
  exact congrArg (fun P : Matrix (Option ι) (Option ι) R => P (some i) (some j)) h

/-- The image preserves the ordinary commutator, not just matrix products. -/
theorem colorEmbedding_lieBracket (M N : Matrix ι ι R) :
    colorEmbeddingHom (lieBracket M N) =
      lieBracket (colorEmbeddingHom M) (colorEmbeddingHom N) := by
  unfold lieBracket
  rw [map_sub, map_mul, map_mul]

/-- The source coordinate is excluded from the image identity. -/
theorem colorEmbedding_one_ne_one [Nontrivial R] :
    colorEmbeddingHom (1 : Matrix ι ι R) ≠ 1 := by
  intro h
  have hentry := congrArg
    (fun P : Matrix (Option ι) (Option ι) R => P none none) h
  change (0 : R) = 1 at hentry
  exact zero_ne_one hentry

variable [StarRing R]

omit [DecidableEq ι] in
theorem colorEmbedding_star (M : Matrix ι ι R) :
    colorEmbeddingHom (star M) = star (colorEmbeddingHom M) := by
  change colorEmbedding M.conjTranspose = (colorEmbedding M).conjTranspose
  ext i j
  cases i <;> cases j <;> simp [colorEmbedding, Matrix.conjTranspose_apply]

end ColorEmbedding

section ExistingRealModels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The abstract embedding sends standard matrix units to the existing color
bosons, fixing the concrete interpretation of its generators. -/
theorem colorEmbedding_single (i j : ι) :
    colorEmbeddingHom (Matrix.single i j (1 : ℝ)) =
      colorBoson forward backward i j := by
  rw [colorBoson_eq_single]
  change colorEmbedding (Matrix.single i j (1 : ℝ)) = _
  ext a b
  cases a <;> cases b <;> simp [colorEmbedding, Matrix.single]

end ExistingRealModels
end InfoGeometry.Core.SupercolorMatrixUnitBridge
