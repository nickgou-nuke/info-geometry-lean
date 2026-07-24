import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter Topology

noncomputable section

/-!
# Nilpotent finite products and their eventually constant limit

This file keeps three lanes separate.

* `recursive_prod` and `recursive_sum` are finite recursive objects.
* `nilpotent_exp T N = 1 + T • N` is the algebraic truncation forced by
  `N * N = 0`; it is not a Taylor-series or analytic-completion definition.
* `finite_to_infinite_limit` is a topological `Tendsto` statement for a sequence
  that is eventually constant.  It does not claim any external Virasoro/Dirac
  completion, functional calculus, or convergence of a nontrivial infinite
  product.
-/

namespace InfoGeometry.Algebra.NilpotentFiniteProductLimit

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Recursive finite product representing the finite-stage inductive transport lane. -/
def recursive_prod (t : ℕ → ℝ) (N : A) : ℕ → A
  | 0 => 1
  | n + 1 => recursive_prod t N n * (1 + t n • N)

/-- Recursive finite sum representing stagewise algebraic parameter accumulation. -/
def recursive_sum (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => recursive_sum t n + t n

/--
The normalized finite product sequence: for nonzero stage `n`, multiply `n`
copies of `1 + (T/n) • N`.
-/
def finite_prod_seq (T : ℝ) (N : A) (n : ℕ) : A :=
  if n = 0 then 1 else recursive_prod (fun _ => T / (n : ℝ)) N n

/-- The algebraic nilpotent exponential truncation `exp_N(T) = 1 + T • N`. -/
def nilpotent_exp (T : ℝ) (N : A) : A :=
  1 + T • N

/-- Recursive sum evaluation for a constant sequence. -/
lemma recursive_sum_const (T : ℝ) (n : ℕ) :
    recursive_sum (fun _ => T) n = (n : ℝ) * T := by
  induction n with
  | zero =>
    unfold recursive_sum
    simp
  | succ k ih =>
    unfold recursive_sum
    rw [ih]
    push_cast
    ring

/-- Summing `n` copies of `T / n` gives exactly `T` when `n ≠ 0`. -/
lemma recursive_sum_div (T : ℝ) (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    recursive_sum (fun _ => T / (n : ℝ)) n = T := by
  rw [recursive_sum_const]
  field_simp [hn]

/--
Finite-stage nilpotent product transport.

If `N * N = 0`, every finite product of factors `1 + t k • N` collapses to
`1 + (recursive_sum t n) • N`.
-/
theorem nilpotent_prod_induction (t : ℕ → ℝ) (N : A) (hN : N * N = 0) (n : ℕ) :
    recursive_prod t N n = 1 + (recursive_sum t n) • N := by
  induction n with
  | zero =>
    unfold recursive_prod recursive_sum
    simp
  | succ k ih =>
    unfold recursive_prod recursive_sum
    rw [ih]
    have h_mul : (1 + (recursive_sum t k) • N) * (1 + (t k) • N) =
        1 + (recursive_sum t k + t k) • N := by
      rw [add_mul, one_mul, mul_add, mul_one]
      have h_smul_mul : ((recursive_sum t k) • N) * ((t k) • N) =
          (recursive_sum t k * t k) • (N * N) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [h_smul_mul, hN, smul_zero]
      rw [add_zero]
      have h_add_smul : (recursive_sum t k) • N + (t k) • N =
          (recursive_sum t k + t k) • N := by
        rw [add_smul]
      rw [← h_add_smul]
      abel
    rw [h_mul]

/-- The normalized finite product is exactly the nilpotent truncation at every positive stage. -/
lemma finite_prod_seq_val (T : ℝ) (N : A) (hN : N * N = 0) (n : ℕ) (hn : n > 0) :
    finite_prod_seq T N n = 1 + T • N := by
  unfold finite_prod_seq
  have hn_ne : n ≠ 0 := by linarith
  rw [if_neg hn_ne]
  rw [nilpotent_prod_induction _ _ hN]
  have hn_real_ne : (n : ℝ) ≠ 0 := by
    have h_pos : (n : ℝ) > 0 := by positivity
    linarith
  rw [recursive_sum_div T n hn_real_ne]

/--
The normalized finite nilpotent products tend to the algebraic nilpotent
truncation because the sequence is eventually constant.
-/
theorem finite_to_infinite_limit (T : ℝ) (N : A) (hN : N * N = 0) :
    Tendsto (fun n : ℕ => finite_prod_seq T N n) atTop (nhds (nilpotent_exp T N)) := by
  unfold nilpotent_exp
  have h_eventually :
      Filter.EventuallyEq atTop (fun n : ℕ => finite_prod_seq T N n) (fun _ => 1 + T • N) := by
    rw [Filter.EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    have hn_gt : n > 0 := by linarith
    exact finite_prod_seq_val T N hN n hn_gt
  exact Filter.tendsto_congr' h_eventually |>.mpr tendsto_const_nhds

/--
Debt marker only: this module proves the eventually-constant nilpotent case;
it does not prove a general infinite-dimensional Hestenes/colimit product
completion or identify the limit with any external Dirac/Virasoro flow.
-/
def general_colimit_completion_debt : String :=
  "Open: prove a general Hestenes/categorical-colimit product-completion theorem beyond the eventually-constant nilpotent case."

end InfoGeometry.Algebra.NilpotentFiniteProductLimit

end
