/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Conditional expectation and information loss in the real matrix tower

The existing diagonal-block average is positive and a bimodule map for
`X ↦ X ⊗ I₂`. Its reembedding is an idempotent linear map, with an explicit
nonzero matrix unit in its kernel. The adjoint square of that matrix unit
has nonzero restriction. No entropy, completion or chiral-pinching identity
is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11ConditionalExpectation

open Matrix
open scoped Kronecker
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet

/-- Restriction of a Kronecker product is its normalized last-factor trace. -/
theorem stageRestrict_kronecker (n : ℕ) (A : MatStage n)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    stageRestrict n (A ⊗ₖ B) = ((B 0 0 + B 1 1) / 2) • A := by
  ext i j
  change (A i j * B 0 0 + A i j * B 1 1) / 2 =
    ((B 0 0 + B 1 1) / 2) * A i j
  ring

/-- Multiplication by an embedded coarse operator pulls through restriction
on the left, without commuting it with the fine operator. -/
theorem stageRestrict_embed_mul (n : ℕ) (A : MatStage n)
    (Y : MatStage (n + 1)) :
    stageRestrict n (stageEmbed n A * Y) = A * stageRestrict n Y := by
  ext i j
  change
    ((∑ k : Idx n × Fin 2,
        (A i k.1 * (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 k.2) * Y k (j, 0)) +
      (∑ k : Idx n × Fin 2,
        (A i k.1 * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 k.2) * Y k (j, 1))) / 2 =
      ∑ k : Idx n, A i k * ((Y (k, 0) (j, 0) + Y (k, 1) (j, 1)) / 2)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    mul_one, mul_zero, zero_mul, add_zero, zero_add]
  calc
    _ = (∑ k : Idx n, (A i k * Y (k, 0) (j, 0) +
        A i k * Y (k, 1) (j, 1))) / 2 := by rw [Finset.sum_add_distrib]
    _ = ∑ k : Idx n, (A i k * Y (k, 0) (j, 0) +
        A i k * Y (k, 1) (j, 1)) / 2 := Finset.sum_div _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The right bimodule law follows from the left law and transpose. -/
theorem stageRestrict_mul_embed (n : ℕ) (Y : MatStage (n + 1))
    (A : MatStage n) :
    stageRestrict n (Y * stageEmbed n A) = stageRestrict n Y * A := by
  have h := stageRestrict_embed_mul n Aᵀ Yᵀ
  have hs : stageEmbed n Aᵀ = (stageEmbed n A)ᵀ := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using stageEmbed_star n A
  rw [hs, ← Matrix.transpose_mul, stageRestrict_transpose] at h
  have ht := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_transpose, Matrix.transpose_mul,
    stageRestrict_transpose] using ht

/-- Restriction is bimodular over the embedded coarse matrix algebra. -/
theorem stageRestrict_bimodule (n : ℕ) (A B : MatStage n)
    (Y : MatStage (n + 1)) :
    stageRestrict n (stageEmbed n A * Y * stageEmbed n B) =
      A * stageRestrict n Y * B := by
  rw [stageRestrict_mul_embed, stageRestrict_embed_mul]

/-- Positive semidefiniteness is preserved by averaging the two principal
blocks. -/
theorem stageRestrict_posSemidef (n : ℕ) {Y : MatStage (n + 1)}
    (hY : Y.PosSemidef) : (stageRestrict n Y).PosSemidef := by
  have h0 := hY.submatrix (fun i : Idx n => (i, (0 : Fin 2)))
  have h1 := hY.submatrix (fun i : Idx n => (i, (1 : Fin 2)))
  have h := (h0.add h1).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1
  ext i j
  change (Y (i, 0) (j, 0) + Y (i, 1) (j, 1)) / 2 =
    (1 / 2 : ℝ) * (Y (i, 0) (j, 0) + Y (i, 1) (j, 1))
  ring

/-- Reembed the existing restriction into the fine matrix algebra. -/
def stageExpectation (n : ℕ) : MatStage (n + 1) →ₗ[ℝ] MatStage (n + 1) :=
  (stageEmbed n).toLinearMap.comp (stageRestrict n)

@[simp] theorem stageExpectation_apply (n : ℕ) (Y : MatStage (n + 1)) :
    stageExpectation n Y = stageEmbed n (stageRestrict n Y) := rfl

/-- Coarse-graining twice agrees with coarse-graining once. -/
theorem stageExpectation_idempotent (n : ℕ) :
    stageExpectation n ∘ₗ stageExpectation n = stageExpectation n := by
  apply LinearMap.ext
  intro Y
  change stageEmbed n (stageRestrict n (stageEmbed n (stageRestrict n Y))) =
    stageEmbed n (stageRestrict n Y)
  rw [stageRestrict_stageEmbed]

/-- Every operator splits into a retained part and a restriction-kernel part. -/
theorem stageRestrict_residual (n : ℕ) (Y : MatStage (n + 1)) :
    stageRestrict n (Y - stageExpectation n Y) = 0 := by
  rw [map_sub, stageExpectation_apply, stageRestrict_stageEmbed, sub_self]

/-- A last-factor off-diagonal matrix unit in the full fine-stage algebra. -/
def fineCreation (n : ℕ) : MatStage (n + 1) :=
  (1 : MatStage n) ⊗ₖ wittCreationBase

/-- The discarded matrix unit is nonzero at every finite stage. -/
theorem fineCreation_ne_zero (n : ℕ) : fineCreation n ≠ 0 := by
  intro h
  have he := congrArg (fun M : MatStage (n + 1) =>
    M (default, 0) (default, 1)) h
  change (1 : MatStage n) default default * 1 = (0 : ℝ) at he
  simp at he

/-- Nilpotency survives tensoring by the coarse identity. -/
theorem fineCreation_sq (n : ℕ) : fineCreation n * fineCreation n = 0 := by
  change ((1 : MatStage n) ⊗ₖ wittCreationBase) *
    ((1 : MatStage n) ⊗ₖ wittCreationBase) =
      (0 : Matrix (Idx n × Fin 2) (Idx n × Fin 2) ℝ)
  rw [← Matrix.mul_kronecker_mul, wittCreationBase_sq]
  simp

@[simp] theorem stageRestrict_fineCreation (n : ℕ) :
    stageRestrict n (fineCreation n) = 0 := by
  rw [fineCreation, stageRestrict_kronecker]
  norm_num [wittCreationBase]

/-- The linear fine-scale mode vanishes, but its positive Gram operator
retains one half of the coarse identity. -/
theorem stageRestrict_fineCreation_gram (n : ℕ) :
    stageRestrict n (star (fineCreation n) * fineCreation n) =
      (1 / 2 : ℝ) • (1 : MatStage n) := by
  have hs : star (fineCreation n) =
      (1 : MatStage n) ⊗ₖ star wittCreationBase := by
    ext ⟨i, a⟩ ⟨j, b⟩
    change star ((1 : MatStage n) j i * wittCreationBase b a) =
      (1 : MatStage n) i j * star (wittCreationBase b a)
    simp [Matrix.one_apply, eq_comm]
  have hm : star (fineCreation n) * fineCreation n =
      (1 : MatStage n) ⊗ₖ (star wittCreationBase * wittCreationBase) := by
    rw [hs]
    change ((1 : MatStage n) ⊗ₖ star wittCreationBase) *
      ((1 : MatStage n) ⊗ₖ wittCreationBase) = _
    rw [← Matrix.mul_kronecker_mul, one_mul]
  rw [hm, stageRestrict_kronecker]
  congr 1
  norm_num [wittCreationBase, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- Reembedding after restriction is not the identity on the fine algebra. -/
theorem stageExpectation_ne_id (n : ℕ) :
    stageExpectation n ≠ LinearMap.id := by
  intro h
  have he := LinearMap.congr_fun h (fineCreation n)
  have hz : (0 : MatStage (n + 1)) = fineCreation n := by simpa using he
  exact fineCreation_ne_zero n hz.symm

/-- The normalized partial trace cannot preserve arbitrary products. -/
theorem stageRestrict_not_multiplicative (n : ℕ) :
    ¬ ∀ X Y : MatStage (n + 1),
      stageRestrict n (X * Y) = stageRestrict n X * stageRestrict n Y := by
  intro h
  have he := h (star (fineCreation n)) (fineCreation n)
  rw [stageRestrict_fineCreation_gram, stageRestrict_fineCreation, mul_zero] at he
  have hd := congrArg (fun M : MatStage n => M default default) he
  norm_num at hd

end InfoGeometry.Canonical.Cl11ConditionalExpectation
