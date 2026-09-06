import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import InfoGeometry.Topology.ConformalSpin
import InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge

/-!
# N-Potent Operator Spectral Hull and Fibonacci Eigenspace

This module formalizes the operator-level spectral theory for $n$-potent endomorphisms:
$T^n = T$ in `Module.End ℂ V`.

## Key Theorems:
1. `end_pow_apply_eigenvector`: $(T^k) v = \lambda^k v$ for any eigenvector $v$.
2. `eigenvalue_pow_eq_self`: If $T^n = T$ and $T v = \lambda v$ with $v \neq 0$, then $\lambda^n = \lambda$.
3. `eigenvalue_pow_sub_one_eq_one`: If $\lambda \neq 0$, then $\lambda^{n-1} = 1$.
4. `six_potent_nonzero_eigenvalue_pow_five`: For $T^6 = T$, any nonzero eigenvalue satisfies $\lambda^5 = 1$.
5. `fibonacci_eigenspace_pow_five`: For $v \in \ker(T - \theta_\tau I)$, $T^5 v = v$.
6. `fibonacci_eigenspace_pow_six`: For $v \in \ker(T - \theta_\tau I)$, $T^6 v = T v$.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Physics.Algebra.NPotentOperatorSpectralHull

open Complex
open InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The $k$-th power of an endomorphism acting on an eigenvector $v$ with eigenvalue `lambdaVal`. -/
theorem end_pow_apply_eigenvector (T : Module.End ℂ V) (v : V) (lambdaVal : ℂ)
    (hv : T v = lambdaVal • v) (k : ℕ) :
    (T ^ k) v = (lambdaVal ^ k) • v := by
  induction k with
  | zero =>
    simp [pow_zero]
  | succ k ih =>
    rw [pow_succ']
    show T ((T ^ k) v) = (lambdaVal ^ (k + 1)) • v
    rw [ih, LinearMap.map_smul, hv, smul_smul, pow_succ, mul_comm]

/-- 🏆 THEOREM: Any eigenvalue of an $n$-potent operator $T^n = T$ satisfies $\lambda^n = \lambda$. -/
theorem eigenvalue_pow_eq_self (T : Module.End ℂ V) (n : ℕ) (hT : T ^ n = T)
    (v : V) (hv_ne : v ≠ 0) (lambdaVal : ℂ) (h_eigen : T v = lambdaVal • v) :
    lambdaVal ^ n = lambdaVal := by
  have h_left : (T ^ n) v = (lambdaVal ^ n) • v := end_pow_apply_eigenvector T v lambdaVal h_eigen n
  have h_right : (T ^ n) v = T v := by rw [hT]
  rw [h_eigen] at h_right
  have h_smul_eq : (lambdaVal ^ n) • v = lambdaVal • v := h_left.symm.trans h_right
  have h_sub : (lambdaVal ^ n - lambdaVal) • v = 0 := by
    rw [sub_smul, h_smul_eq, sub_self]
  have h_scalar := smul_eq_zero.mp h_sub
  cases h_scalar with
  | inl h_zero => exact sub_eq_zero.mp h_zero
  | inr h_v_zero => exact False.elim (hv_ne h_v_zero)

/-- 🏆 THEOREM: Any NONZERO eigenvalue of an $n$-potent operator satisfies $\lambda^{n-1} = 1$ (for $n \ge 2$). -/
theorem eigenvalue_pow_sub_one_eq_one (T : Module.End ℂ V) (n : ℕ) (hn : 2 ≤ n) (hT : T ^ n = T)
    (v : V) (hv_ne : v ≠ 0) (lambdaVal : ℂ) (h_ne : lambdaVal ≠ 0) (h_eigen : T v = lambdaVal • v) :
    lambdaVal ^ (n - 1) = 1 := by
  have h_poly : hullPoly n lambdaVal = 0 := by
    dsimp [hullPoly]
    have h_pow := eigenvalue_pow_eq_self T n hT v hv_ne lambdaVal h_eigen
    exact sub_eq_zero.mpr h_pow
  exact (n_potent_root_iff n hn lambdaVal h_ne).mp h_poly

/-- 🏆 THEOREM: For a 6-potent operator $T^6 = T$, any nonzero eigenvalue satisfies $\lambda^5 = 1$. -/
theorem six_potent_nonzero_eigenvalue_pow_five (T : Module.End ℂ V) (hT : T ^ 6 = T)
    (v : V) (hv_ne : v ≠ 0) (lambdaVal : ℂ) (h_ne : lambdaVal ≠ 0) (h_eigen : T v = lambdaVal • v) :
    lambdaVal ^ 5 = 1 := by
  have h := eigenvalue_pow_sub_one_eq_one T 6 (by norm_num) hT v hv_ne lambdaVal h_ne h_eigen
  exact h

/-- 🏆 THEOREM: Action of $T^5$ on the Fibonacci eigenspace $\ker(T - \theta_\tau I)$ is the identity. -/
theorem fibonacci_eigenspace_pow_five (T : Module.End ℂ V) (v : V)
    (hv : v ∈ fibonacciEigenspace T) :
    (T ^ 5) v = v := by
  rw [mem_fibonacciEigenspace_iff] at hv
  have h_pow := end_pow_apply_eigenvector T v fibonacciTopologicalTwist hv 5
  have h_twist5 := fibonacci_twist_pow_five
  rw [h_twist5, one_smul] at h_pow
  exact h_pow

/-- 🏆 THEOREM: Action of $T^6$ on the Fibonacci eigenspace $\ker(T - \theta_\tau I)$ equals $T v$. -/
theorem fibonacci_eigenspace_pow_six (T : Module.End ℂ V) (v : V)
    (hv : v ∈ fibonacciEigenspace T) :
    (T ^ 6) v = T v := by
  rw [mem_fibonacciEigenspace_iff] at hv
  have h_pow := end_pow_apply_eigenvector T v fibonacciTopologicalTwist hv 6
  have h_twist6 := fibonacci_twist_six_potent
  rw [h_twist6, ← hv] at h_pow
  exact h_pow

/-- Eigenspace invariance under power iterations. -/
theorem fibonacci_eigenspace_invariant_pow (T : Module.End ℂ V) (k : ℕ) (v : V)
    (hv : v ∈ fibonacciEigenspace T) :
    (T ^ k) v = (fibonacciTopologicalTwist ^ k) • v := by
  rw [mem_fibonacciEigenspace_iff] at hv
  exact end_pow_apply_eigenvector T v fibonacciTopologicalTwist hv k

end InfoGeometry.Physics.Algebra.NPotentOperatorSpectralHull
