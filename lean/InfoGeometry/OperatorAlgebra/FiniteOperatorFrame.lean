/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite operator multipliers and rectangular Gram identities

The coefficient ring may be noncommutative. Rectangular matrix multiplication
gives the synthesis/analysis identities without a scalar inner-product model.
For an operator family, its frame sum is the existing Kraus channel evaluated
at `1`; the multiplier permits a separate operator-valued symbol at each index.

These are finite algebraic statements. A Gaussian Gabor frame, convergence of
an infinite lattice sum, and a fractal uncertainty estimate require additional
analytic constructions. In particular, the Gram-square identity below is not
Knutsen's Lemma 5.2, which concerns Gaussian sampling and an operator norm.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteOperatorFrame

open Matrix
open scoped BigOperators
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

variable {B : Type*} [Ring B] [StarRing B]

section Rectangular

variable {ι κ : Type*} [Fintype ι]

/-- The frame and Gram operators intertwine through the actual rectangular
synthesis matrix. -/
theorem synthesis_gram_intertwining [Fintype κ] (S : Matrix κ ι B) :
    (S * Sᴴ) * S = S * (Sᴴ * S) :=
  Matrix.mul_assoc S Sᴴ S

variable [DecidableEq ι]

/-- A finite operator-valued diagonal symbol acts between synthesis and
analysis. The multiplication order is part of the definition. -/
def matrixMultiplier (S : Matrix κ ι B) (b : ι → B) : Matrix κ κ B :=
  S * diagonal b * Sᴴ

theorem matrixMultiplier_apply (S : Matrix κ ι B) (b : ι → B) (r s : κ) :
    matrixMultiplier S b r s = ∑ i, S r i * b i * star (S s i) := by
  rw [matrixMultiplier, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

theorem matrixMultiplier_adjoint (S : Matrix κ ι B) (b : ι → B) :
    (matrixMultiplier S b)ᴴ = matrixMultiplier S (fun i => star (b i)) := by
  simp only [matrixMultiplier, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_assoc]
  rfl

theorem matrixMultiplier_add (S : Matrix κ ι B) (b c : ι → B) :
    matrixMultiplier S (b + c) = matrixMultiplier S b + matrixMultiplier S c := by
  ext r s
  simp only [Matrix.add_apply, matrixMultiplier_apply, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem matrixMultiplier_one (S : Matrix κ ι B) :
    matrixMultiplier S (fun _ => 1) = S * Sᴴ := by
  simp [matrixMultiplier]

/-- Complementary symbols recover the frame operator. No order or positivity
is asserted for a general star ring. -/
theorem matrixMultiplier_complement (S : Matrix κ ι B) (b : ι → B) :
    matrixMultiplier S b + matrixMultiplier S (fun i => 1 - b i) = S * Sᴴ := by
  rw [← matrixMultiplier_add]
  have h : b + (fun i => 1 - b i) = fun _ => 1 := by
    funext i
    simp only [Pi.add_apply]
    abel
  rw [h, matrixMultiplier_one]

variable [Fintype κ] [DecidableEq κ]

/-- Every positive Gram power is a rectangular transport of a frame power.
The exponent shift is necessary: at exponent zero the two identities live
on different matrix index types. -/
theorem gram_pow_succ (S : Matrix κ ι B) (n : ℕ) :
    (Sᴴ * S) ^ (n + 1) = Sᴴ * (S * Sᴴ) ^ n * S := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (Sᴴ * S) ^ (n + 1 + 1) = (Sᴴ * S) ^ (n + 1) * (Sᴴ * S) :=
        pow_succ _ _
      _ = (Sᴴ * (S * Sᴴ) ^ n * S) * (Sᴴ * S) := by rw [ih]
      _ = Sᴴ * ((S * Sᴴ) ^ n * (S * Sᴴ)) * S := by
        simp only [Matrix.mul_assoc]
      _ = Sᴴ * (S * Sᴴ) ^ (n + 1) * S := by rw [pow_succ]

/-- The adjoint rectangular transport gives the corresponding frame powers. -/
theorem frame_pow_succ (S : Matrix κ ι B) (n : ℕ) :
    (S * Sᴴ) ^ (n + 1) = S * (Sᴴ * S) ^ n * Sᴴ := by
  simpa only [Matrix.conjTranspose_conjTranspose] using gram_pow_succ Sᴴ n

omit [DecidableEq ι] in
/-- The coisometry equation makes the Gram operator a native star projection.
This algebraic statement allows noncommutative operator coefficients. -/
theorem gram_isStarProjection_of_coisometry (S : Matrix κ ι B)
    (hS : S * Sᴴ = 1) : IsStarProjection (Sᴴ * S) where
  isIdempotentElem := by
    change (Sᴴ * S) * (Sᴴ * S) = Sᴴ * S
    calc
      _ = Sᴴ * (S * Sᴴ) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS, Matrix.mul_one]
  isSelfAdjoint := by
    change (Sᴴ * S)ᴴ = Sᴴ * S
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

end Rectangular

section OperatorFamilies

variable {ι : Type*} [Fintype ι]

/-- Finite synthesis with a separate operator-valued symbol at every index. -/
def multiplier (φ b : ι → B) : B :=
  ∑ i, φ i * b i * star (φ i)

/-- Constant symbols recover the pre-existing finite Kraus operator. -/
theorem multiplier_const (φ : ι → B) (x : B) :
    multiplier φ (fun _ => x) = krausChannel φ x := rfl

theorem multiplier_add (φ b c : ι → B) :
    multiplier φ (b + c) = multiplier φ b + multiplier φ c := by
  simp only [multiplier, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem multiplier_star (φ b : ι → B) :
    star (multiplier φ b) = multiplier φ (fun i => star (b i)) := by
  simp only [multiplier, star_sum, star_mul, star_star, mul_assoc]

theorem multiplier_complement (φ b : ι → B) :
    multiplier φ b + multiplier φ (fun i => 1 - b i) = krausChannel φ 1 := by
  rw [← multiplier_add]
  have h : b + (fun i => 1 - b i) = fun _ => 1 := by
    funext i
    simp only [Pi.add_apply]
    abel
  rw [h, multiplier_const]

/-- A finite zero/one symbol is the corresponding partial frame sum. -/
theorem multiplier_indicator [DecidableEq ι] (φ : ι → B) (s : Finset ι) :
    multiplier φ (fun i => if i ∈ s then 1 else 0) =
      ∑ i ∈ s, φ i * star (φ i) := by
  simp [multiplier, mul_ite, ite_mul]

/-- The frame sum is self-adjoint even when its coefficients do not commute. -/
theorem frame_isSelfAdjoint (φ : ι → B) : IsSelfAdjoint (krausChannel φ 1) := by
  rw [krausChannel_one]
  change star (∑ i, φ i * star (φ i)) = ∑ i, φ i * star (φ i)
  simp only [star_sum, star_mul, star_star]

/-- The native matrix Gramian of an operator-valued family. -/
def gram (φ : ι → B) : Matrix ι ι B :=
  Matrix.of fun i j => star (φ i) * φ j

omit [Fintype ι] in
@[simp] theorem gram_apply (φ : ι → B) (i j : ι) :
    gram φ i j = star (φ i) * φ j := rfl

omit [Fintype ι] in
/-- The family Gramian is exactly the adjoint-times-synthesis product for
its one-row rectangular synthesis matrix. -/
theorem gram_eq_adjoint_synthesis (φ : ι → B) :
    gram φ =
      (Matrix.of (fun (_ : Unit) i => φ i))ᴴ *
        (Matrix.of (fun (_ : Unit) i => φ i)) := by
  ext i j
  simp [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Operator-valued multipliers are the one-row case of the rectangular
diagonal-symbol construction. -/
theorem multiplier_eq_matrixMultiplier [DecidableEq ι] (φ b : ι → B) :
    multiplier φ b =
      matrixMultiplier (Matrix.of (fun (_ : Unit) i => φ i)) b () () := by
  rw [matrixMultiplier_apply]
  rfl

omit [Fintype ι] in
theorem gram_isSelfAdjoint (φ : ι → B) : IsSelfAdjoint (gram φ) := by
  change (gram φ)ᴴ = gram φ
  ext i j
  simp only [Matrix.conjTranspose_apply, gram_apply, star_mul, star_star]

/-- The Gram square remembers the full ordered frame sum between its two
operator coefficients. -/
theorem gram_sq_apply (φ : ι → B) (i j : ι) :
    (gram φ * gram φ) i j = star (φ i) * krausChannel φ 1 * φ j := by
  rw [Matrix.mul_apply, krausChannel_one, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [gram_apply, mul_assoc]

/-- Matrix trace here retains its value in the possibly noncommutative
coefficient ring. No cyclic trace identity is used. -/
theorem trace_gram (φ : ι → B) :
    Matrix.trace (gram φ) = ∑ i, star (φ i) * φ i := rfl

/-- Parseval completeness produces a self-adjoint idempotent Gram matrix. -/
theorem gram_isStarProjection_of_parseval (φ : ι → B)
    (hφ : krausChannel φ 1 = 1) : IsStarProjection (gram φ) where
  isIdempotentElem := by
    change gram φ * gram φ = gram φ
    ext i j
    rw [gram_sq_apply, hφ, mul_one, gram_apply]
  isSelfAdjoint := gram_isSelfAdjoint φ

end OperatorFamilies

end InfoGeometry.OperatorAlgebra.FiniteOperatorFrame
