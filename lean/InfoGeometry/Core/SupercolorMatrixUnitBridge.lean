/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorSourceClosure
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
open InfoGeometry.Core.SupercolorSourceClosure
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

theorem colorEmbedding_injective :
    Function.Injective (colorEmbeddingHom (ι := ι) (R := R)) := by
  intro M N h
  ext i j
  exact congrArg (fun P : Matrix (Option ι) (Option ι) R => P (some i) (some j)) h

/-- The image preserves the ordinary commutator, not just matrix products. -/
theorem colorEmbedding_lieBracket (M N : Matrix ι ι R) :
    colorEmbeddingHom (lieBracket M N) =
      lieBracket (colorEmbeddingHom M) (colorEmbeddingHom N) := by
  simp only [lieBracket, map_sub, map_mul]

/-- The source coordinate is excluded from the image identity. -/
theorem colorEmbedding_one_ne_one [Nontrivial R] :
    colorEmbeddingHom (1 : Matrix ι ι R) ≠ 1 := by
  intro h
  have hentry := congrArg
    (fun P : Matrix (Option ι) (Option ι) R => P none none) h
  simpa [colorEmbeddingHom, colorEmbedding] using hentry

variable [StarRing R]

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

/-- Noncommutativity is witnessed by different diagonal matrix units. -/
theorem orthogonal_pair_noncommutes (i : ι) :
    orthogonalForward i * orthogonalBackward i ≠
      orthogonalBackward i * orthogonalForward i := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (ι × Bool) (ι × Bool) ℝ => M (i, true) (i, true)) h
  simp [orthogonalForward, orthogonalBackward, Matrix.single] at hentry

/-- The disjoint realization supplies the star assertions requested in the
note without duplicating any of its existing operators or MP predicates. -/
theorem orthogonal_star_certificate :
    star (totalCentralCharge (orthogonalForward (ι := ι)) orthogonalBackward) =
        totalCentralCharge orthogonalForward orthogonalBackward ∧
    star (totalMajoranaPlus (orthogonalForward (ι := ι)) orthogonalBackward) =
        totalMajoranaPlus orthogonalForward orthogonalBackward ∧
    star (totalMajoranaMinus (orthogonalForward (ι := ι)) orthogonalBackward) =
        -totalMajoranaMinus orthogonalForward orthogonalBackward := by
  exact ⟨total_charge_star_of_mp orthogonal_matrix_supercolor.mp,
    star_totalMajoranaPlus_of_dual orthogonalBackward_eq_star_forward,
    star_totalMajoranaMinus_of_dual orthogonalBackward_eq_star_forward⟩

/-- Nonzero disjoint sectors do not satisfy the common-source specification. -/
theorem orthogonal_not_common_absorption {i j : ι} (hij : i ≠ j) :
    ¬ (orthogonalForward i * (orthogonalBackward j * orthogonalForward j) =
      orthogonalForward i) := by
  intro h
  have hz := (orthogonal_absorption_forces_zero orthogonal_matrix_supercolor hij h).1
  have hentry := congrArg
    (fun M : Matrix (ι × Bool) (ι × Bool) ℝ => M (i, true) (i, false)) hz
  simp [orthogonalForward, Matrix.single] at hentry

/-- The common-source model realizes the odd module action on actual arrows. -/
theorem common_source_odd_actions (i j l : ι) :
    lieBracket (colorBoson forward backward i j) (forward l) =
        (if j = l then forward i else 0) ∧
    lieBracket (colorBoson forward backward i j) (backward l) =
        -(if l = i then backward j else 0) := by
  apply colorBoson_odd_actions matrix_supercolor
    (q := Matrix.single none none (1 : ℝ))
  intro a
  simp [forward, backward]

/-- Two-color witness: the matrices really are noncommutative, while the two
existing total charges retain their star and signed-square identities. -/
theorem fin2_noncommutative_star_certificate :
    (∀ i : Fin 2, orthogonalForward i * orthogonalBackward i ≠
      orthogonalBackward i * orthogonalForward i) ∧
    star (totalMajoranaPlus (orthogonalForward (ι := Fin 2)) orthogonalBackward) =
      totalMajoranaPlus orthogonalForward orthogonalBackward ∧
    star (totalMajoranaMinus (orthogonalForward (ι := Fin 2)) orthogonalBackward) =
      -totalMajoranaMinus orthogonalForward orthogonalBackward := by
  exact ⟨orthogonal_pair_noncommutes, orthogonal_star_certificate.2⟩

/-- Four-color version on the existing eight-coordinate matrix carrier. -/
theorem fin4_noncommutative_star_certificate :
    (∀ i : Fin 4, orthogonalForward i * orthogonalBackward i ≠
      orthogonalBackward i * orthogonalForward i) ∧
    star (totalMajoranaPlus (orthogonalForward (ι := Fin 4)) orthogonalBackward) =
      totalMajoranaPlus orthogonalForward orthogonalBackward ∧
    star (totalMajoranaMinus (orthogonalForward (ι := Fin 4)) orthogonalBackward) =
      -totalMajoranaMinus orthogonalForward orthogonalBackward := by
  exact ⟨orthogonal_pair_noncommutes, orthogonal_star_certificate.2⟩

end ExistingRealModels
end InfoGeometry.Core.SupercolorMatrixUnitBridge
