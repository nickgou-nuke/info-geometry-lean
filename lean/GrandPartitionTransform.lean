import GrandPartitionPolynomial
import Mathlib

noncomputable section

open Polynomial Finset
open scoped BigOperators

section TransformLayer

variable {R : Type*} [CommRing R]

/-- Evaluation of the finite grand-partition polynomial at activity `q`. -/
def grandPartition (n : ℕ) (q : R) (b : ℕ → R) : R :=
  (grandPartitionPoly b n).eval q

/-- Product representation of the evaluated grand partition function. -/
theorem grandPartition_eq_product (n : ℕ) (q : R) (b : ℕ → R) :
    grandPartition n q b = ∏ i ∈ range n, (1 + q * b i) := by
  induction n with
  | zero =>
      simp [grandPartition, grandPartitionPoly]
  | succ n ih =>
      rw [grandPartition, grandPartitionPoly, eval_mul, eval_add, eval_one,
        eval_mul, eval_C, eval_X, Finset.prod_range_succ]
      change grandPartition n q b * (1 + b n * q) =
        (∏ i ∈ range n, (1 + q * b i)) * (1 + q * b n)
      rw [ih]
      ring

/-- Coefficient representation of the evaluated grand partition function. -/
theorem grandPartition_eq_sum (n : ℕ) (q : R) (b : ℕ → R) :
    grandPartition n q b =
      ∑ m ∈ range (n + 1), q ^ m * canonicalPartition b n m := by
  rw [grandPartition, grandPartitionPoly_as_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- Division-free prior normalization.  The relation between prior `α` and
activity `q` is supplied as the ring identity `α = (1 - α)q`. -/
theorem prior_normalization_of_relation
    (n : ℕ) (α q : R) (b : ℕ → R)
    (hαq : α = (1 - α) * q) :
    (∏ i ∈ range n, ((1 - α) + α * b i)) =
      (1 - α) ^ n * grandPartition n q b := by
  calc
    (∏ i ∈ range n, ((1 - α) + α * b i)) =
        ∏ i ∈ range n, ((1 - α) * (1 + q * b i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hib : α * b i = ((1 - α) * q) * b i :=
            congrArg (fun x => x * b i) hαq
          rw [hib]
          ring
    _ = (∏ _i ∈ range n, (1 - α)) *
        (∏ i ∈ range n, (1 + q * b i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (1 - α) ^ n * grandPartition n q b := by
          rw [grandPartition_eq_product]
          simp

end TransformLayer

section ZTransformLayer

variable {K : Type*} [Field K]

/-- Finite unilateral Z-transform convention `X(z) = Ξ(z⁻¹)`. -/
def unilateralZTransform (n : ℕ) (z : K) (b : ℕ → K) : K :=
  grandPartition n z⁻¹ b

theorem unilateralZTransform_eq_sum
    (n : ℕ) (z : K) (b : ℕ → K) :
    unilateralZTransform n z b =
      ∑ m ∈ range (n + 1), canonicalPartition b n m * z⁻¹ ^ m := by
  rw [unilateralZTransform, grandPartition_eq_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_comm]

end ZTransformLayer

section DiscreteLaplaceLayer

/-- The finite discrete Laplace transform, represented without a convergence
condition because the canonical sequence has finite support. -/
def discreteLaplace (n : ℕ) (s : ℝ) (b : ℕ → ℝ) : ℝ :=
  grandPartition n (Real.exp (-s)) b

theorem discreteLaplace_eq_sum
    (n : ℕ) (s : ℝ) (b : ℕ → ℝ) :
    discreteLaplace n s b =
      ∑ m ∈ range (n + 1), (Real.exp (-s)) ^ m * canonicalPartition b n m := by
  exact grandPartition_eq_sum n (Real.exp (-s)) b

end DiscreteLaplaceLayer
