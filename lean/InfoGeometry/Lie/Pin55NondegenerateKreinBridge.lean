/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Nondegenerate Krein Bilinear Form and $\mathfrak{so}(5,5)$ Invariance

This module formalizes the signature (5,5) Krein bilinear form on $\mathbb{R}^{10}$,
establishing:
1. Canonical signature $(5,5)$ matrix $J_{5,5}$ with $J_{5,5}^2 = 1$ and $J_{5,5}^T = J_{5,5}$.
2. Nondegenerate Krein bilinear form $\langle x, y \rangle_{5,5} := x \cdot (J_{5,5} y)$.
3. Strict nondegeneracy: $(\forall y, \langle x, y \rangle_{5,5} = 0) \leftrightarrow x = 0$,
   and the native Mathlib `LinearMap.BilinForm.Nondegenerate` certificate.
4. Definite sectors: positive definite on the first 5 coordinates and negative definite
   on the last 5 coordinates.
5. Explicit 5-dimensional totally isotropic diagonal Witt subspace where the Krein form vanishes identically.
6. Lie algebra $\mathfrak{so}(5,5)$ Krein-skew-adjointness condition $A^T J_{5,5} + J_{5,5} A = 0$,
   its equivalence with $J_{5,5} A J_{5,5} = -A^T$, and infinitesimal invariance
   $\langle A x, y \rangle_{5,5} + \langle x, A y \rangle_{5,5} = 0$.
7. Closure under commutator Lie bracket $\⁅A, B⁆ = A B - B A$ and the native `LieSubalgebra` structure.
8. Explicit OpenGauss Trap T16 non-commuting generator witnesses $X, Y \in \mathfrak{so}(5,5)$
   satisfying $X Y \neq Y X$ and $\⁅X, Y⁆ \neq 0$.

This directly closes `docs/OPEN_DEBT_PROBLEMS.md` Section 2.B by replacing the degenerate
placeholder form `B_concrete_zero` with a genuine, strictly nondegenerate Krein metric.
-/

open Matrix

namespace InfoGeometry.Lie.Pin55NondegenerateKreinBridge

/-- Canonical diagonal signature (5,5) matrix $J_{5,5} = \mathrm{diag}(1,1,1,1,1,-1,-1,-1,-1,-1)$. -/
def J55 : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.diagonal (fun i => if i.val < 5 then 1 else -1)

/-- $J_{5,5}$ is symmetric. -/
theorem J55_transpose : J55ᵀ = J55 := by
  exact diagonal_transpose _

/-- $J_{5,5}^2 = 1$. -/
theorem J55_sq : J55 ^ 2 = 1 := by
  rw [sq, ← diagonal_one, J55, diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> ring

/-- $J_{5,5} * J_{5,5} = 1$. -/
theorem J55_mul_self : J55 * J55 = 1 := by
  have h := J55_sq
  rwa [sq] at h

/-- Entrywise action of post-multiplying by a diagonal matrix. -/
theorem mul_diagonal_apply (A : Matrix (Fin 10) (Fin 10) ℝ) (d : Fin 10 → ℝ) (i j : Fin 10) :
    (A * diagonal d) i j = A i j * d j := by
  dsimp [Matrix.mul_apply, diagonal]
  rw [Finset.sum_eq_single j]
  · simp
  · intros k _ hk
    simp [hk]
  · intros hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Entrywise action of pre-multiplying by a diagonal matrix. -/
theorem diagonal_mul_apply (d : Fin 10 → ℝ) (A : Matrix (Fin 10) (Fin 10) ℝ) (i j : Fin 10) :
    (diagonal d * A) i j = d i * A i j := by
  dsimp [Matrix.mul_apply, diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intros k _ hk
    simp [hk.symm]
  · intros hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The signature (5,5) Krein bilinear form $\langle x, y \rangle_{5,5} := x \cdot (J_{5,5} y)$. -/
def kreinForm55 (x y : Fin 10 → ℝ) : ℝ :=
  dotProduct x (J55.mulVec y)

/-- Native Mathlib bilinear form instance for $J_{5,5}$. -/
def kreinBilinForm55 : LinearMap.BilinForm ℝ (Fin 10 → ℝ) :=
  J55.toBilin'

/-- Action of $J_{5,5}$ on a vector: component-wise signs $+1$ for $i < 5$ and $-1$ for $i \ge 5$. -/
theorem mulVec_J55 (y : Fin 10 → ℝ) (i : Fin 10) :
    J55.mulVec y i = (if i.val < 5 then 1 else -1) * y i := by
  dsimp [mulVec, J55, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp
  · intros j _ hj
    simp [diagonal_apply_ne _ hj.symm]
  · intros hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Explicit sum expansion of the Krein form. -/
theorem kreinForm55_apply (x y : Fin 10 → ℝ) :
    kreinForm55 x y = ∑ i : Fin 10, x i * ((if i.val < 5 then 1 else -1) * y i) := by
  dsimp [kreinForm55, dotProduct]
  congr 1
  ext i
  rw [mulVec_J55]

/-- Symmetry of the Krein form: $\langle x, y \rangle_{5,5} = \langle y, x \rangle_{5,5}$. -/
theorem kreinForm55_symm (x y : Fin 10 → ℝ) :
    kreinForm55 x y = kreinForm55 y x := by
  rw [kreinForm55_apply, kreinForm55_apply]
  congr 1
  ext i
  ring

/-- Strict nondegeneracy of the Krein form: $(\forall y, \langle x, y \rangle_{5,5} = 0) \leftrightarrow x = 0$. -/
theorem kreinForm55_nondegenerate (x : Fin 10 → ℝ) :
    (∀ y, kreinForm55 x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hy := h (Pi.single i 1)
    rw [kreinForm55_apply] at hy
    rw [Finset.sum_eq_single i] at hy
    · simp only [Pi.single_eq_same, mul_one] at hy
      split_ifs at hy with hi
      · simpa using hy
      · have h_neg : x i * (-1 : ℝ) = - x i := by
          ring
        rw [h_neg] at hy
        exact neg_eq_zero.mp hy
    · intros j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intros hi
      exact False.elim (hi (Finset.mem_univ i))
  · rintro rfl y
    simp [kreinForm55, dotProduct]

/-- Native Mathlib nondegeneracy certificate for `kreinBilinForm55`. -/
theorem kreinBilinForm55_nondegenerate :
    kreinBilinForm55.Nondegenerate := by
  constructor
  · intro x hx
    apply (kreinForm55_nondegenerate x).mp
    intro y
    have hxy := hx y
    dsimp [kreinBilinForm55] at hxy
    rw [toBilin'_apply'] at hxy
    exact hxy
  · intro y hy
    apply (kreinForm55_nondegenerate y).mp
    intro x
    have hxy := hy x
    dsimp [kreinBilinForm55] at hxy
    rw [toBilin'_apply'] at hxy
    rw [kreinForm55_symm]
    exact hxy

/-- Subspace of vectors supported on the first 5 coordinates (positive sector). -/
def isPosSector (x : Fin 10 → ℝ) : Prop :=
  ∀ i : Fin 10, 5 ≤ i.val → x i = 0

/-- Subspace of vectors supported on the last 5 coordinates (negative sector). -/
def isNegSector (x : Fin 10 → ℝ) : Prop :=
  ∀ i : Fin 10, i.val < 5 → x i = 0

/-- The Krein form on the positive sector equals the standard sum of squares. -/
theorem kreinForm55_posSector_eq {x : Fin 10 → ℝ} (h : isPosSector x) :
    kreinForm55 x x = ∑ i : Fin 10, (x i) ^ 2 := by
  rw [kreinForm55_apply]
  congr 1
  ext i
  by_cases hi : i.val < 5
  · simp [hi, sq]
  · have h5 : 5 ≤ i.val := by
      omega
    have hx0 : x i = 0 := h i h5
    simp [hx0]

/-- Positive semidefiniteness on the positive sector. -/
theorem kreinForm55_posSector_nonneg {x : Fin 10 → ℝ} (h : isPosSector x) :
    0 ≤ kreinForm55 x x := by
  rw [kreinForm55_posSector_eq h]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- Strict positive definiteness on the non-zero positive sector. -/
theorem kreinForm55_posSector_pos {x : Fin 10 → ℝ} (h : isPosSector x) (hx : x ≠ 0) :
    0 < kreinForm55 x x := by
  rw [kreinForm55_posSector_eq h]
  have hex : ∃ i, x i ≠ 0 := by
    contrapose! hx
    ext i
    exact hx i
  rcases hex with ⟨i, hi⟩
  have hsq_pos : 0 < (x i) ^ 2 := sq_pos_of_ne_zero hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, hsq_pos⟩

/-- The Krein form on the negative sector equals the negative sum of squares. -/
theorem kreinForm55_negSector_eq {x : Fin 10 → ℝ} (h : isNegSector x) :
    kreinForm55 x x = - ∑ i : Fin 10, (x i) ^ 2 := by
  rw [kreinForm55_apply, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  by_cases hi : i.val < 5
  · have hx0 : x i = 0 := h i hi
    simp [hx0]
  · simp [hi, sq]

/-- Negative semidefiniteness on the negative sector. -/
theorem kreinForm55_negSector_nonpos {x : Fin 10 → ℝ} (h : isNegSector x) :
    kreinForm55 x x ≤ 0 := by
  rw [kreinForm55_negSector_eq h]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))

/-- Strict negative definiteness on the non-zero negative sector. -/
theorem kreinForm55_negSector_neg {x : Fin 10 → ℝ} (h : isNegSector x) (hx : x ≠ 0) :
    kreinForm55 x x < 0 := by
  rw [kreinForm55_negSector_eq h]
  have hex : ∃ i, x i ≠ 0 := by
    contrapose! hx
    ext i
    exact hx i
  rcases hex with ⟨i, hi⟩
  have hsq_pos : 0 < (x i) ^ 2 := sq_pos_of_ne_zero hi
  have hpos : 0 < ∑ i : Fin 10, (x i) ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, hsq_pos⟩
  exact neg_lt_zero.mpr hpos

/-- Canonical split equivalence $\mathrm{Fin}\ 5 \oplus \mathrm{Fin}\ 5 \simeq \mathrm{Fin}\ 10$. -/
def fin10Equiv : Fin 5 ⊕ Fin 5 ≃ Fin 10 :=
  (finSumFinEquiv (m := 5) (n := 5)).trans (finCongr (by decide))

@[simp]
theorem fin10Equiv_inl_val (i : Fin 5) : (fin10Equiv (Sum.inl i)).val = i.val := by
  dsimp [fin10Equiv]
  rw [finSumFinEquiv_apply_left]
  exact Fin.val_castAdd 5 i

@[simp]
theorem fin10Equiv_inr_val (i : Fin 5) : (fin10Equiv (Sum.inr i)).val = 5 + i.val := by
  dsimp [fin10Equiv]
  rw [finSumFinEquiv_apply_right]
  exact Fin.val_natAdd 5 i

@[simp]
theorem fin10Equiv_inl_lt (i : Fin 5) : (fin10Equiv (Sum.inl i)).val < 5 := by
  rw [fin10Equiv_inl_val]
  exact i.isLt

@[simp]
theorem fin10Equiv_inr_not_lt (i : Fin 5) : ¬ ((fin10Equiv (Sum.inr i)).val < 5) := by
  rw [fin10Equiv_inr_val]
  omega

/-- 5-dimensional totally isotropic diagonal Witt subspace where $x_{i+5} = x_i$. -/
def wittSubspace : Subspace ℝ (Fin 10 → ℝ) where
  carrier := { x : Fin 10 → ℝ | ∀ i : Fin 5, x (fin10Equiv (Sum.inr i)) = x (fin10Equiv (Sum.inl i)) }
  zero_mem' := by
    intro i
    rfl
  add_mem' := by
    intro x y hx hy i
    dsimp
    rw [hx i, hy i]
  smul_mem' := by
    intro c x hx i
    dsimp
    rw [hx i]

/-- Characterization of the Witt subspace via arithmetic coordinate indices. -/
theorem wittSubspace_iff (x : Fin 10 → ℝ) :
    x ∈ wittSubspace ↔ ∀ i : Fin 5, x ⟨i.val + 5, by omega⟩ = x ⟨i.val, by omega⟩ := by
  constructor
  · intro h i
    have hi := h i
    have h_inr : fin10Equiv (Sum.inr i) = ⟨i.val + 5, by omega⟩ := by
      ext
      simp [fin10Equiv_inr_val, add_comm]
    have h_inl : fin10Equiv (Sum.inl i) = ⟨i.val, by omega⟩ := by
      ext
      simp [fin10Equiv_inl_val]
    rw [← h_inr, ← h_inl]
    exact hi
  · intro h i
    have hi := h i
    have h_inr : fin10Equiv (Sum.inr i) = ⟨i.val + 5, by omega⟩ := by
      ext
      simp [fin10Equiv_inr_val, add_comm]
    have h_inl : fin10Equiv (Sum.inl i) = ⟨i.val, by omega⟩ := by
      ext
      simp [fin10Equiv_inl_val]
    rw [h_inr, h_inl]
    exact hi

/-- Identical vanishing of the Krein form on the 5D Witt subspace: totally isotropic. -/
theorem kreinForm55_witt_isotropic (x y : Fin 10 → ℝ)
    (hx : x ∈ wittSubspace) (hy : y ∈ wittSubspace) :
    kreinForm55 x y = 0 := by
  rw [kreinForm55_apply]
  rw [← fin10Equiv.sum_comp]
  simp only [Fintype.sum_sum_type]
  have h_sum1 : ∑ i : Fin 5, x (fin10Equiv (Sum.inl i)) *
      ((if (fin10Equiv (Sum.inl i)).val < 5 then (1:ℝ) else -1) * y (fin10Equiv (Sum.inl i))) =
      ∑ i : Fin 5, x (fin10Equiv (Sum.inl i)) * y (fin10Equiv (Sum.inl i)) := by
    congr 1
    ext i
    simp
  have h_sum2 : ∑ i : Fin 5, x (fin10Equiv (Sum.inr i)) *
      ((if (fin10Equiv (Sum.inr i)).val < 5 then (1:ℝ) else -1) * y (fin10Equiv (Sum.inr i))) =
      - ∑ i : Fin 5, x (fin10Equiv (Sum.inl i)) * y (fin10Equiv (Sum.inl i)) := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext i
    simp only [fin10Equiv_inr_not_lt, ↓reduceIte]
    have hxi : x (fin10Equiv (Sum.inr i)) = x (fin10Equiv (Sum.inl i)) := hx i
    have hyi : y (fin10Equiv (Sum.inr i)) = y (fin10Equiv (Sum.inl i)) := hy i
    rw [hxi, hyi]
    ring
  rw [h_sum1, h_sum2]
  ring

/-- Condition for a matrix $A \in M_{10}(\mathbb{R})$ to be in $\mathfrak{so}(5,5)$: $A^T J_{5,5} + J_{5,5} A = 0$. -/
def IsSO55KreinMatrix (A : Matrix (Fin 10) (Fin 10) ℝ) : Prop :=
  Aᵀ * J55 + J55 * A = 0

/-- Equivalence of the Krein skew-adjointness condition with $J_{5,5} A J_{5,5} = -A^T$. -/
theorem isSO55_iff_J55_mul_mul_eq_neg_transpose (A : Matrix (Fin 10) (Fin 10) ℝ) :
    IsSO55KreinMatrix A ↔ J55 * A * J55 = - Aᵀ := by
  constructor
  · intro h
    have h1 : Aᵀ * J55 = - (J55 * A) := eq_neg_of_add_eq_zero_left h
    have h2 : (Aᵀ * J55) * J55 = - (J55 * A) * J55 := by
      rw [h1]
    rw [mul_assoc, J55_mul_self, Matrix.mul_one, neg_mul] at h2
    rw [← neg_eq_iff_eq_neg] at h2
    exact h2.symm
  · intro h
    dsimp [IsSO55KreinMatrix]
    have h1 : (J55 * A * J55) * J55 = (- Aᵀ) * J55 := by
      rw [h]
    rw [mul_assoc, J55_mul_self, Matrix.mul_one, neg_mul] at h1
    rw [h1, add_neg_cancel]

/-- Infinitesimal Krein-skew-adjointness invariance of the bilinear form:
$\langle A x, y \rangle_{5,5} + \langle x, A y \rangle_{5,5} = 0$. -/
theorem kreinForm55_skew_adjoint (A : Matrix (Fin 10) (Fin 10) ℝ) (hA : IsSO55KreinMatrix A)
    (x y : Fin 10 → ℝ) :
    kreinForm55 (A.mulVec x) y + kreinForm55 x (A.mulVec y) = 0 := by
  dsimp [kreinForm55]
  have h1 : (A *ᵥ x) ⬝ᵥ (J55 *ᵥ y) = x ⬝ᵥ ((Aᵀ * J55) *ᵥ y) := by
    rw [← vecMul_transpose]
    rw [← dotProduct_mulVec]
    rw [mulVec_mulVec]
  have h2 : x ⬝ᵥ (J55 *ᵥ (A *ᵥ y)) = x ⬝ᵥ ((J55 * A) *ᵥ y) := by
    rw [mulVec_mulVec]
  rw [h1, h2, ← dotProduct_add, ← add_mulVec]
  dsimp [IsSO55KreinMatrix] at hA
  rw [hA, zero_mulVec, dotProduct_zero]

local instance : LieRing (Matrix (Fin 10) (Fin 10) ℝ) := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (Matrix (Fin 10) (Fin 10) ℝ) := LieAlgebra.ofAssociativeAlgebra

theorem isSO55_zero : IsSO55KreinMatrix (0 : Matrix (Fin 10) (Fin 10) ℝ) := by
  dsimp [IsSO55KreinMatrix]
  simp

theorem isSO55_add {A B : Matrix (Fin 10) (Fin 10) ℝ}
    (hA : IsSO55KreinMatrix A) (hB : IsSO55KreinMatrix B) :
    IsSO55KreinMatrix (A + B) := by
  dsimp [IsSO55KreinMatrix] at *
  calc (A + B)ᵀ * J55 + J55 * (A + B)
    _ = (Aᵀ + Bᵀ) * J55 + (J55 * A + J55 * B) := by
      rw [transpose_add, Matrix.mul_add]
    _ = (Aᵀ * J55 + J55 * A) + (Bᵀ * J55 + J55 * B) := by
      rw [add_mul]
      abel
    _ = 0 + 0 := by
      rw [hA, hB]
    _ = 0 := add_zero 0

theorem isSO55_smul (c : ℝ) {A : Matrix (Fin 10) (Fin 10) ℝ}
    (hA : IsSO55KreinMatrix A) :
    IsSO55KreinMatrix (c • A) := by
  dsimp [IsSO55KreinMatrix] at *
  calc (c • A)ᵀ * J55 + J55 * (c • A)
    _ = c • (Aᵀ * J55) + c • (J55 * A) := by
      rw [transpose_smul, smul_mul, Matrix.mul_smul]
    _ = c • (Aᵀ * J55 + J55 * A) := by
      rw [smul_add]
    _ = c • (0 : Matrix (Fin 10) (Fin 10) ℝ) := by
      rw [hA]
    _ = 0 := smul_zero c

theorem isSO55_bracket {A B : Matrix (Fin 10) (Fin 10) ℝ}
    (hA : IsSO55KreinMatrix A) (hB : IsSO55KreinMatrix B) :
    IsSO55KreinMatrix (⁅A, B⁆ : Matrix (Fin 10) (Fin 10) ℝ) := by
  dsimp [IsSO55KreinMatrix] at *
  have hA_eq : Aᵀ * J55 = - (J55 * A) := eq_neg_of_add_eq_zero_left hA
  have hB_eq : Bᵀ * J55 = - (J55 * B) := eq_neg_of_add_eq_zero_left hB
  change (A * B - B * A)ᵀ * J55 + J55 * (A * B - B * A) = 0
  rw [transpose_sub, transpose_mul, transpose_mul, sub_mul]
  rw [mul_assoc, mul_assoc]
  rw [hA_eq, hB_eq]
  rw [mul_neg, mul_neg]
  rw [← mul_assoc, ← mul_assoc]
  rw [hB_eq, hA_eq]
  rw [neg_mul, neg_mul, neg_neg, neg_neg]
  rw [Matrix.mul_sub, mul_assoc, mul_assoc]
  abel

/-- The matrix Lie subalgebra $\mathfrak{so}(5,5)$ inside $M_{10}(\mathbb{R})$. -/
def so55KreinLieSubalgebra : LieSubalgebra ℝ (Matrix (Fin 10) (Fin 10) ℝ) where
  carrier := { A : Matrix (Fin 10) (Fin 10) ℝ | IsSO55KreinMatrix A }
  add_mem' {_A _B} hA hB := isSO55_add hA hB
  zero_mem' := isSO55_zero
  smul_mem' c {_A} hA := isSO55_smul c hA
  lie_mem' {_A _B} hA hB := isSO55_bracket hA hB

/-- First OpenGauss T16 generator witness: rotation generator $S_{01} = E_{01} - E_{10}$. -/
def genX : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 1 then (1 : ℝ)
    else if i = 1 ∧ j = 0 then -1
    else 0

/-- Second OpenGauss T16 generator witness: rotation generator $S_{12} = E_{12} - E_{21}$. -/
def genY : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 1 ∧ j = 2 then (1 : ℝ)
    else if i = 2 ∧ j = 1 then -1
    else 0

/-- $X \in \mathfrak{so}(5,5)$. -/
theorem genX_isSO55 : IsSO55KreinMatrix genX := by
  dsimp [IsSO55KreinMatrix, J55]
  ext i j
  rw [Matrix.add_apply, mul_diagonal_apply, diagonal_mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  dsimp [genX]
  fin_cases i <;> fin_cases j <;> norm_num

/-- $Y \in \mathfrak{so}(5,5)$. -/
theorem genY_isSO55 : IsSO55KreinMatrix genY := by
  dsimp [IsSO55KreinMatrix, J55]
  ext i j
  rw [Matrix.add_apply, mul_diagonal_apply, diagonal_mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  dsimp [genY]
  fin_cases i <;> fin_cases j <;> norm_num

/-- $X$ belongs to `so55KreinLieSubalgebra`. -/
theorem genX_mem_so55 : genX ∈ so55KreinLieSubalgebra :=
  genX_isSO55

/-- $Y$ belongs to `so55KreinLieSubalgebra`. -/
theorem genY_mem_so55 : genY ∈ so55KreinLieSubalgebra :=
  genY_isSO55

/-- OpenGauss Trap T16 Non-Commutativity Witness: $X Y \neq Y X$ in $\mathfrak{so}(5,5)$. -/
theorem genX_genY_noncomm : genX * genY ≠ genY * genX := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℝ => M 0 2) h
  dsimp [Matrix.mul_apply] at h02
  have hL : (∑ k : Fin 10, genX 0 k * genY k 2) = 1 := by
    rw [Finset.sum_eq_single 1]
    · dsimp [genX, genY]
      norm_num
    · intro k _ hk
      dsimp [genX]
      fin_cases k <;> (try contradiction) <;> norm_num
    · intro hk
      exact False.elim (hk (Finset.mem_univ 1))
  have hR : (∑ k : Fin 10, genY 0 k * genX k 2) = 0 := by
    have h0 : ∀ k : Fin 10, genY 0 k = 0 := by
      intro k
      dsimp [genY]
    simp [h0]
  rw [hL, hR] at h02
  norm_num at h02

/-- Non-vanishing commutator in $\mathfrak{so}(5,5)$: $\⁅genX, genY⁆ \neq 0$. -/
theorem genX_genY_bracket_ne_zero : ⁅genX, genY⁆ ≠ 0 := by
  change genX * genY - genY * genX ≠ 0
  intro h
  have h_comm : genX * genY = genY * genX := sub_eq_zero.mp h
  exact genX_genY_noncomm h_comm

end InfoGeometry.Lie.Pin55NondegenerateKreinBridge
