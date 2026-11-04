/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CayleyForm
import InfoGeometry.Krein.ChiralTransposeLift
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# An exact boundary between Krein conservation and depth stability

On the existing doubled real carrier, an explicit Cayley transform preserves
the diagonal Krein form while multiplying a nonzero null direction by three.
Its powers therefore have unbounded positive energy. A second generator shows
why the denominator inverse in the general Cayley theorem cannot be omitted.
These are finite matrix counterexamples, not substitutes for the general
noncommutative preservation theorem.
-/

noncomputable section

namespace InfoGeometry.Krein.CayleyGrowthObstruction

open Matrix
open InfoGeometry.Algebra.CayleyForm
open InfoGeometry.Krein.ChiralTransposeLift

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The swap is skew-adjoint for the diagonal indefinite form. -/
theorem swap_skew_for_grading :
    (laggedCoincidenceSwap (n := n)).transpose * laggedCoincidenceGrading +
      laggedCoincidenceGrading * laggedCoincidenceSwap = 0 := by
  simp only [laggedCoincidenceSwap, laggedCoincidenceGrading,
    fromBlocks_transpose, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

/-- The negative half-swap is in the domain of the displayed Cayley transform. -/
def generator : DoubledLaggedMatrix n :=
  (-1 / 2 : ℝ) • laggedCoincidenceSwap

/-- An actual inverse witness; no totalized matrix inverse is used. -/
def denominatorInverse : DoubledLaggedMatrix n :=
  (4 / 3 : ℝ) • 1 + (2 / 3 : ℝ) • laggedCoincidenceSwap

/-- A rational boost whose plus null direction is multiplied by three. -/
def boost : DoubledLaggedMatrix n :=
  (5 / 3 : ℝ) • 1 + (4 / 3 : ℝ) • laggedCoincidenceSwap

theorem generator_skew_for_grading :
    star (generator (n := n)) * laggedCoincidenceGrading +
      laggedCoincidenceGrading * generator = 0 := by
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    generator, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  rw [swap_skew_for_grading, smul_zero]

theorem denominator_right_inverse :
    (1 + generator (n := n)) * denominatorInverse = 1 := by
  simp only [generator, denominatorInverse, mul_add, add_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, one_mul, mul_one, laggedCoincidenceSwap_square]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem cayley_eq_boost :
    (1 - generator (n := n)) * denominatorInverse = boost := by
  simp only [generator, denominatorInverse, boost, sub_mul, mul_add, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, one_mul, mul_one, laggedCoincidenceSwap_square]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Conservation follows from the generic noncommutative Cayley theorem. -/
theorem boost_preserves_grading :
    (boost (n := n)).transpose * laggedCoincidenceGrading * boost =
      laggedCoincidenceGrading := by
  have h := cayley_preserves_form laggedCoincidenceGrading (generator (n := n))
    denominatorInverse generator_skew_for_grading denominator_right_inverse
  simpa only [cayley_eq_boost, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem boost_pow_preserves_grading (k : ℕ) :
    ((boost (n := n)) ^ k).transpose * laggedCoincidenceGrading * boost ^ k =
      laggedCoincidenceGrading := by
  have h : star (boost (n := n)) * laggedCoincidenceGrading * boost =
      laggedCoincidenceGrading := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using boost_preserves_grading (n := n)
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using pow_preserves_form laggedCoincidenceGrading boost h k

/-- The same vector on both sheets is a null direction of the diagonal form. -/
def duplicate (v : n → ℝ) : n ⊕ n → ℝ := Sum.elim v v

theorem duplicate_krein_null (v : n → ℝ) :
    duplicate v ⬝ᵥ (laggedCoincidenceGrading *ᵥ duplicate v) = 0 := by
  simp [duplicate, laggedCoincidenceGrading, fromBlocks_mulVec,
    Matrix.neg_mulVec, dotProduct, Fintype.sum_sum_type]

theorem swap_mulVec_duplicate (v : n → ℝ) :
    laggedCoincidenceSwap *ᵥ duplicate v = duplicate v := by
  simp [duplicate, laggedCoincidenceSwap, fromBlocks_mulVec]

theorem boost_mulVec_duplicate (v : n → ℝ) :
    boost *ᵥ duplicate v = (3 : ℝ) • duplicate v := by
  rw [boost, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, swap_mulVec_duplicate]
  rw [← add_smul]
  norm_num

theorem boost_pow_mulVec_duplicate (v : n → ℝ) (k : ℕ) :
    boost ^ k *ᵥ duplicate v = (3 : ℝ) ^ k • duplicate v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, boost_mulVec_duplicate,
        smul_smul, pow_succ]

/-- Positive Euclidean energy grows by nine at every step despite form conservation. -/
theorem boost_pow_energy (v : n → ℝ) (k : ℕ) :
    (boost ^ k *ᵥ duplicate v) ⬝ᵥ (boost ^ k *ᵥ duplicate v) =
      (9 : ℝ) ^ k * (duplicate v ⬝ᵥ duplicate v) := by
  rw [boost_pow_mulVec_duplicate, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- A concrete nonempty direction rules out any depth-independent energy bound. -/
theorem boost_energy_unbounded (bound : ℝ) :
    ∃ k : ℕ,
      bound < ((boost (n := Unit)) ^ k *ᵥ duplicate (fun _ => (1 : ℝ))) ⬝ᵥ
        ((boost (n := Unit)) ^ k *ᵥ duplicate (fun _ => (1 : ℝ))) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (bound / 2) (show (1 : ℝ) < 9 by norm_num)
  refine ⟨k, ?_⟩
  rw [boost_pow_energy]
  have henergy : duplicate (fun _ : Unit => (1 : ℝ)) ⬝ᵥ duplicate (fun _ => (1 : ℝ)) = 2 := by
    simp [duplicate, dotProduct]
  rw [henergy]
  linarith

/-- The minus null projection annihilates the singular Cayley denominator. -/
theorem nullMinus_mul_one_add_swap :
    nullMinus (n := n) * (1 + laggedCoincidenceSwap) = 0 := by
  rw [mul_add, mul_one, nullMinus_blocks]
  simp only [Matrix.smul_mul, laggedCoincidenceSwap, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

theorem nullMinus_ne_zero [Nonempty n] : nullMinus (n := n) ≠ 0 := by
  intro h
  let i : n := Classical.choice inferInstance
  have hi := congrArg (fun A : DoubledLaggedMatrix n => A (Sum.inl i) (Sum.inl i)) h
  norm_num [nullMinus_blocks, fromBlocks] at hi

/-- A form-skew generator can have a Cayley denominator with no right inverse. -/
theorem one_add_swap_has_no_right_inverse [Nonempty n] :
    ¬ ∃ r : DoubledLaggedMatrix n, (1 + laggedCoincidenceSwap) * r = 1 := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun A : DoubledLaggedMatrix n => nullMinus * A) hr
  rw [← mul_assoc, nullMinus_mul_one_add_swap, zero_mul, mul_one] at h
  exact nullMinus_ne_zero h.symm

end InfoGeometry.Krein.CayleyGrowthObstruction
