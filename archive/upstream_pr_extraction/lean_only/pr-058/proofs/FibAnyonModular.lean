import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable section

namespace FibAnyonModular

inductive FibLabel where
| I
| tau
deriving DecidableEq, Fintype

open FibLabel
open Matrix
open scoped BigOperators

variable {K : Type*} [CommRing K]

structure FibonacciCyclotomicData (K : Type*) [CommRing K] where
zeta : K
sqrtTau : K
cyclotomic :
zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1 = 0
sqrtTau_sq :
sqrtTau ^ 2 = zeta ^ 2 - zeta ^ 3

def goldenTau (D : FibonacciCyclotomicData K) : K :=
D.zeta ^ 2 - D.zeta ^ 3

lemma zeta_pow_five (D : FibonacciCyclotomicData K) :
D.zeta ^ 5 = -1 := by
  linear_combination (D.zeta + 1) * D.cyclotomic

lemma zeta_pow_ten (D : FibonacciCyclotomicData K) :
D.zeta ^ 10 = 1 := by
  calc
    D.zeta ^ 10 = (D.zeta ^ 5) ^ 2 := by ring
    _ = (-1 : K) ^ 2 := by rw [zeta_pow_five D]
    _ = 1 := by ring

lemma goldenTau_quadratic (D : FibonacciCyclotomicData K) :
goldenTau D * goldenTau D + goldenTau D = 1 := by
  unfold goldenTau
  linear_combination (D.zeta ^ 2 - D.zeta - 1) * D.cyclotomic

lemma goldenTau_sq (D : FibonacciCyclotomicData K) :
  goldenTau D ^ 2 = 1 - goldenTau D := by
  have h := goldenTau_quadratic D
  linear_combination h

@[simp]
lemma sum_fib_label (f : FibLabel → K) :
(∑ x : FibLabel, f x) = f I + f tau := by
  classical
  have huniv :
  (Finset.univ : Finset FibLabel) = {I, tau} := by
    ext x
    cases x <;> simp
  rw [huniv]
  simp

def fibQuantumDim
(D : FibonacciCyclotomicData K) :
FibLabel → K
| I => 1
| tau => 1 + goldenTau D

def FibSUnnormalized
(D : FibonacciCyclotomicData K) :
Matrix FibLabel FibLabel K
| I, I => 1
| I, tau => fibQuantumDim D tau
| tau, I => fibQuantumDim D tau
| tau, tau => -1

def FibT
(D : FibonacciCyclotomicData K) :
Matrix FibLabel FibLabel K
| I, I => 1
| tau, tau => D.zeta ^ 4
| _, _ => 0

def FibTInv
(D : FibonacciCyclotomicData K) :
Matrix FibLabel FibLabel K
| I, I => 1
| tau, tau => D.zeta ^ 6
| _, _ => 0

def fibTotalDimSq
(D : FibonacciCyclotomicData K) : K :=
1 + fibQuantumDim D tau ^ 2

def fibGaussSumPlus
(D : FibonacciCyclotomicData K) : K :=
1 + fibQuantumDim D tau ^ 2 * D.zeta ^ 4

def fibGaussSumMinus
(D : FibonacciCyclotomicData K) : K :=
1 + fibQuantumDim D tau ^ 2 * D.zeta ^ 6

lemma fibQuantumDim_tau_sq
(D : FibonacciCyclotomicData K) :
fibQuantumDim D tau ^ 2 =
fibQuantumDim D tau + 1 := by
  simp only [fibQuantumDim]
  linear_combination goldenTau_quadratic D

lemma fibTotalDimSq_eq
(D : FibonacciCyclotomicData K) :
fibTotalDimSq D = 3 + goldenTau D := by
  unfold fibTotalDimSq
  rw [fibQuantumDim_tau_sq D]
  simp [fibQuantumDim]
  ring

lemma fib_twist_fifth_power
(D : FibonacciCyclotomicData K) :
(D.zeta ^ 4) ^ 5 = 1 := by
  calc
    (D.zeta ^ 4) ^ 5 = (D.zeta ^ 10) ^ 2 := by ring
    _ = 1 := by rw [zeta_pow_ten D]; ring

lemma fib_twist_inverse
(D : FibonacciCyclotomicData K) :
D.zeta ^ 4 * D.zeta ^ 6 = 1 := by
  calc
    D.zeta ^ 4 * D.zeta ^ 6 = D.zeta ^ 10 := by ring
    _ = 1 := zeta_pow_ten D

lemma fib_twist_inverse_rev
(D : FibonacciCyclotomicData K) :
D.zeta ^ 6 * D.zeta ^ 4 = 1 := by
  calc
    D.zeta ^ 6 * D.zeta ^ 4 =
    D.zeta ^ 4 * D.zeta ^ 6 := by ring
    _ = 1 := fib_twist_inverse D

lemma fib_gauss_sum_product
(D : FibonacciCyclotomicData K) :
fibGaussSumPlus D * fibGaussSumMinus D =
fibTotalDimSq D := by
  unfold fibGaussSumPlus fibGaussSumMinus fibTotalDimSq
  simp only [fibQuantumDim]
  unfold goldenTau
  linear_combination (D.zeta ^ 18 - 3 * D.zeta ^ 17 + 2 * D.zeta ^ 16 - 2 * D.zeta ^ 15 + 5 * D.zeta ^ 14 + D.zeta ^ 12 - 4 * D.zeta ^ 11 - 4 * D.zeta ^ 10 - 3 * D.zeta ^ 9 + D.zeta ^ 8 + 2 * D.zeta ^ 7 + 5 * D.zeta ^ 6 + 3 * D.zeta ^ 5 + 2 * D.zeta ^ 4 - 2 * D.zeta ^ 2 - D.zeta - 1) * D.cyclotomic

theorem fib_S_square
(D : FibonacciCyclotomicData K) :
FibSUnnormalized D * FibSUnnormalized D =
Matrix.diagonal
(fun _ : FibLabel => fibTotalDimSq D) := by
  ext i j
  cases i <;> cases j <;>
  simp [FibSUnnormalized, Matrix.mul_apply, sum_fib_label]
  all_goals
    dsimp only [goldenTau, fibQuantumDim, fibGaussSumPlus, fibTotalDimSq]
    ring_nf

theorem fib_T_fifth_power
(D : FibonacciCyclotomicData K) :
FibT D ^ 5 = 1 := by
  have h :
  FibT D ^ 5 =
  FibT D * FibT D * FibT D * FibT D * FibT D := by
    simp only [pow_succ, pow_zero, one_mul]
  have htwist :
  D.zeta ^ 4 * D.zeta ^ 4 * D.zeta ^ 4 *
  D.zeta ^ 4 * D.zeta ^ 4 = 1 := by
    calc
      D.zeta ^ 4 * D.zeta ^ 4 * D.zeta ^ 4 *
      D.zeta ^ 4 * D.zeta ^ 4 =
      (D.zeta ^ 4) ^ 5 := by ring
      _ = 1 := fib_twist_fifth_power D
  rw [h]
  ext i j
  cases i <;> cases j
  · simp [FibT, Matrix.one_apply, Matrix.mul_apply, sum_fib_label]
  · simp [FibT, Matrix.one_apply, Matrix.mul_apply, sum_fib_label]
  · simp [FibT, Matrix.one_apply, Matrix.mul_apply, sum_fib_label]
  · simpa [FibT, Matrix.one_apply, Matrix.mul_apply, sum_fib_label] using htwist

theorem fib_T_mul_TInv
(D : FibonacciCyclotomicData K) :
FibT D * FibTInv D = 1 := by
  ext i j
  cases i <;> cases j <;>
  simp [FibT, FibTInv, Matrix.mul_apply, Matrix.one_apply, sum_fib_label, fib_twist_inverse D]

theorem fib_TInv_mul_T
(D : FibonacciCyclotomicData K) :
FibTInv D * FibT D = 1 := by
  ext i j
  cases i <;> cases j <;>
  simp [FibT, FibTInv, Matrix.mul_apply, Matrix.one_apply, sum_fib_label, fib_twist_inverse D, fib_twist_inverse_rev D]

theorem fib_ST_cube_diagonal
(D : FibonacciCyclotomicData K) :
(FibSUnnormalized D * FibT D) ^ 3 =
Matrix.diagonal
(fun _ : FibLabel =>
fibGaussSumPlus D * fibTotalDimSq D) := by
  ext i j
  cases i <;> cases j
  · simp [FibSUnnormalized, FibT, Matrix.mul_apply, sum_fib_label, pow_succ, pow_zero]
    dsimp only [goldenTau, fibQuantumDim, fibGaussSumPlus, fibTotalDimSq]
    ring_nf
    linear_combination (-D.zeta ^ 12 + 3 * D.zeta ^ 11 - 3 * D.zeta ^ 10 + 3 * D.zeta ^ 9 - 4 * D.zeta ^ 8 + D.zeta ^ 7 + 2 * D.zeta ^ 5 + D.zeta ^ 4 - 2 * D.zeta ^ 2 - D.zeta - 1) * D.cyclotomic
  · simp [FibSUnnormalized, FibT, Matrix.mul_apply, sum_fib_label, pow_succ, pow_zero]
    dsimp only [goldenTau, fibQuantumDim, fibGaussSumPlus, fibTotalDimSq]
    ring_nf
    linear_combination (-D.zeta ^ 13 + 2 * D.zeta ^ 12 - D.zeta ^ 11 + D.zeta ^ 10 - D.zeta ^ 9 - D.zeta ^ 8 + D.zeta ^ 6 + D.zeta ^ 5 + D.zeta ^ 4) * D.cyclotomic
  · simp [FibSUnnormalized, FibT, Matrix.mul_apply, sum_fib_label, pow_succ, pow_zero]
    dsimp only [goldenTau, fibQuantumDim, fibGaussSumPlus, fibTotalDimSq]
    ring_nf
    linear_combination (-D.zeta ^ 9 + 2 * D.zeta ^ 8 - D.zeta ^ 7 + D.zeta ^ 6 - D.zeta ^ 5 - D.zeta ^ 4 + D.zeta ^ 2 + D.zeta + 1) * D.cyclotomic
  · simp [FibSUnnormalized, FibT, Matrix.mul_apply, sum_fib_label, pow_succ, pow_zero]
    dsimp only [goldenTau, fibQuantumDim, fibGaussSumPlus, fibTotalDimSq]
    ring_nf
    linear_combination (-D.zeta ^ 12 + 3 * D.zeta ^ 11 - 4 * D.zeta ^ 10 + 4 * D.zeta ^ 9 - 4 * D.zeta ^ 8 + D.zeta ^ 7 - D.zeta ^ 6 + 2 * D.zeta ^ 5 - 2 * D.zeta ^ 2 - 2 * D.zeta - 2) * D.cyclotomic

theorem fib_projective_modular_relation
(D : FibonacciCyclotomicData K) :
(FibSUnnormalized D * FibT D) ^ 3 =
fibGaussSumPlus D •
(FibSUnnormalized D * FibSUnnormalized D) := by
  rw [fib_ST_cube_diagonal D, fib_S_square D]
  ext i j
  cases i <;> cases j <;>
  simp

def FibFusionTau
(D : FibonacciCyclotomicData K) :
Matrix FibLabel FibLabel K
| I, I => 0
| I, tau => 1
| tau, I => 1
| tau, tau => 1

def FibFusionEigenvalues
(D : FibonacciCyclotomicData K) :
Matrix FibLabel FibLabel K :=
Matrix.diagonal
  (fun
    | I => fibQuantumDim D tau
    | tau => -goldenTau D)

theorem fib_fusion_diagonalized_by_S
(D : FibonacciCyclotomicData K) :
FibFusionTau D * FibSUnnormalized D =
FibSUnnormalized D * FibFusionEigenvalues D := by
  ext i j
  cases i <;> cases j <;>
  simp [FibFusionTau, FibFusionEigenvalues, FibSUnnormalized, Matrix.mul_apply, sum_fib_label, fibQuantumDim]
  · linear_combination -1 * goldenTau_quadratic D
  · linear_combination -1 * goldenTau_quadratic D

theorem fib_fusion_ring_relation
(D : FibonacciCyclotomicData K) :
FibFusionTau D * FibFusionTau D =
(1 : Matrix FibLabel FibLabel K) + FibFusionTau D := by
  ext i j
  cases i <;> cases j <;>
    simp [FibFusionTau, Matrix.one_apply, Matrix.mul_apply, Matrix.add_apply, sum_fib_label]

theorem fib_fusion_commutes_S_square
(D : FibonacciCyclotomicData K) :
FibFusionTau D * (FibSUnnormalized D * FibSUnnormalized D) =
(FibSUnnormalized D * FibSUnnormalized D) * FibFusionTau D := by
  rw [fib_S_square D]
  ext i j
  cases i <;> cases j <;>
    simp [FibFusionTau, Matrix.mul_apply, Matrix.diagonal, sum_fib_label, fibTotalDimSq]

end FibAnyonModular
