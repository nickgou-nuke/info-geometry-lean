/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.FiniteMatrixGibbsParity

/-!
# Growing finite onsite Hamiltonians in the native matrix tower

The new tensor factor carries the existing Pauli tilt/switch matrices. Onsite
increments centralize the old matrix algebra, so their commutators intertwine
the native successor embedding. Nonzero weights act nontrivially on each fresh
tail. This file asserts no norm bound, completion, or coupled-interaction model.
-/
noncomputable section
open scoped Kronecker

namespace InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian

open CuntzMatrixTowerInstantiation CuntzMatrixTraceTower
open InfoGeometry.Physics.KleinBottleSewingExact

/-- The actual final tensor factor, on the existing native stage carrier. -/
def tailEmbedding (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] MatrixStage (n + 1) where
  toFun B := (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n))
    ((1 : MatrixStage n) ⊗ₖ B)
  map_one' := by simp
  map_mul' B D := by
    have h := Matrix.mul_kronecker_mul (1 : MatrixStage n) (1 : MatrixStage n) B D
    simp only [one_mul] at h
    rw [h]
    exact (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).map_mul _ _
  map_zero' := by simp
  map_add' B D := by
    rw [Matrix.kronecker_add]
    exact (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).map_add _ _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [Matrix.kronecker_smul]
  map_star' B := by
    ext i j
    rcases hi : (stageIndexEquiv n).symm i with ⟨i₁, i₂⟩
    rcases hj : (stageIndexEquiv n).symm j with ⟨j₁, j₂⟩
    by_cases hij : i₁ = j₁
    · subst j₁
      simp [Matrix.reindexAlgEquiv, Matrix.star_apply, hi, hj]
    · simp [Matrix.reindexAlgEquiv, Matrix.star_apply, hi, hj,
        hij, Ne.symm hij]

def tailZ (n : ℕ) : MatrixStage (n + 1) := tailEmbedding n tilt2
def tailX (n : ℕ) : MatrixStage (n + 1) := tailEmbedding n switch2

/-- The old factor and the fresh factor commute for arbitrary matrices. -/
theorem concreteStep_commutes_tail (n : ℕ) (A : MatrixStage n)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : Commute (concreteStep n A) (tailEmbedding n B) := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)) (A ⊗ₖ 1) *
      (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)) (1 ⊗ₖ B) =
    (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)) (1 ⊗ₖ B) *
      (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)) (A ⊗ₖ 1)
  rw [← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem tailZ_commutes_concreteStep (n : ℕ) (A : MatrixStage n) :
    Commute (tailZ n) (concreteStep n A) :=
  (concreteStep_commutes_tail n A tilt2).symm

theorem tailX_commutes_concreteStep (n : ℕ) (A : MatrixStage n) :
    Commute (tailX n) (concreteStep n A) :=
  (concreteStep_commutes_tail n A switch2).symm

theorem tailZ_isHermitian (n : ℕ) : (tailZ n).IsHermitian := by
  have hz : tilt2.IsHermitian := by
    simpa using FiniteMatrixGibbsFunctional.tiltHamiltonian_isHermitian (1 : ℝ)
  change star (tailEmbedding n tilt2) = tailEmbedding n tilt2
  rw [← map_star]
  exact congrArg (tailEmbedding n) hz

/-- Arbitrary real onsite weights, without a summability or normalization premise. -/
def onsiteHamiltonian (w : ℕ → ℝ) : (n : ℕ) → MatrixStage n
  | 0 => 0
  | n + 1 => concreteStep n (onsiteHamiltonian w n) + w n • tailZ n

@[simp] theorem onsiteHamiltonian_zero (w : ℕ → ℝ) : onsiteHamiltonian w 0 = 0 := rfl
@[simp] theorem onsiteHamiltonian_succ (w : ℕ → ℝ) (n : ℕ) :
    onsiteHamiltonian w (n + 1) = concreteStep n (onsiteHamiltonian w n) + w n • tailZ n := rfl

theorem onsiteHamiltonian_isHermitian (w : ℕ → ℝ) (n : ℕ) :
    (onsiteHamiltonian w n).IsHermitian := by
  induction n with
  | zero => simp [onsiteHamiltonian, Matrix.IsHermitian]
  | succ n ih =>
    have ihstar : star (onsiteHamiltonian w n) = onsiteHamiltonian w n := ih
    have hzstar : star (tailZ n) = tailZ n := tailZ_isHermitian n
    change star (concreteStep n (onsiteHamiltonian w n) + w n • tailZ n) =
      concreteStep n (onsiteHamiltonian w n) + w n • tailZ n
    rw [star_add, ← map_star, ihstar, star_smul, star_trivial, hzstar]

/-- Successor compatibility is derived from centralization of the old algebra. -/
theorem onsite_commutator_successor (w : ℕ → ℝ) (n : ℕ) (A : MatrixStage n) :
    onsiteHamiltonian w (n + 1) * concreteStep n A -
        concreteStep n A * onsiteHamiltonian w (n + 1) =
      concreteStep n (onsiteHamiltonian w n * A - A * onsiteHamiltonian w n) := by
  rw [onsiteHamiltonian_succ, map_sub, map_mul, map_mul, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, (tailZ_commutes_concreteStep n A).eq]
  abel

/-- The old Hamiltonian contributes nothing to the new tail commutator. -/
theorem onsite_fresh_tail_action (w : ℕ → ℝ) (n : ℕ) :
    onsiteHamiltonian w (n + 1) * tailX n - tailX n * onsiteHamiltonian w (n + 1) =
      w n • tailEmbedding n (tilt2 * switch2 - switch2 * tilt2) := by
  have ht : tailZ n * tailX n - tailX n * tailZ n =
      tailEmbedding n (tilt2 * switch2 - switch2 * tilt2) := by
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [onsiteHamiltonian_succ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    (tailX_commutes_concreteStep n (onsiteHamiltonian w n)).eq, ← ht, smul_sub]
  abel

/-- A specific fresh off-diagonal entry detects every nonzero real weight. -/
theorem weighted_tail_commutator_ne_zero (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    c • tailEmbedding n (tilt2 * switch2 - switch2 * tilt2) ≠ 0 := by
  intro hzero
  have he := congrArg (fun M : MatrixStage (n + 1) =>
    M (stageIndexEquiv n ((0 : Fin (2 ^ n)), 0))
      (stageIndexEquiv n ((0 : Fin (2 ^ n)), 1))) hzero
  have hr := congrArg Complex.re he
  norm_num [tailEmbedding, Matrix.reindexAlgEquiv, tilt2, switch2,
    Matrix.mul_apply, Fin.sum_univ_two, RCLike.real_smul_eq_coe_mul] at hr
  exact hc (by linarith)

/-- Genuine fresh-stage action, not an ill-typed comparison across stage carriers. -/
theorem onsite_fresh_tail_action_ne_zero (w : ℕ → ℝ) (n : ℕ) (hw : w n ≠ 0) :
    onsiteHamiltonian w (n + 1) * tailX n - tailX n * onsiteHamiltonian w (n + 1) ≠ 0 := by
  rw [onsite_fresh_tail_action]
  exact weighted_tail_commutator_ne_zero n (w n) hw

end InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian
