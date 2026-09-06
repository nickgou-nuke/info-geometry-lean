import InfoGeometry.Clifford.SplitQuaternion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic

set_option autoImplicit false

open Filter Topology

/-!
# Split-quaternion nilpotent finite-product flow

This file translates the normalized nilpotent finite-product lane into the
existing split-quaternion model.  The nilpotent generator is the concrete
split-quaternion `N = i - j`.

The limit theorem is coordinatewise and eventually-constant: it proves that the
normalized finite products are eventually equal to `1 + T • (i - j)` in the
four real coordinates.  It does not assert a general analytic completion,
functional calculus, Virasoro/Dirac limit, or topological ring structure on the
split quaternions beyond the explicit coordinatewise `Tendsto` predicate below.
-/

namespace InfoGeometry.Clifford.SplitQuaternionNilpotentFlow

@[simp] theorem sq_add_def (q r : SplitQuaternion) : q + r = sqAdd q r := rfl
@[simp] theorem sq_mul_def (q r : SplitQuaternion) : q * r = sqMul q r := rfl
@[simp] theorem sq_one_def : (1 : SplitQuaternion) = sqOne := rfl
@[simp] theorem sq_zero_def : (0 : SplitQuaternion) = sqZero := rfl

/-- Scalar multiplication over the split-quaternion coordinate space. -/
def sq_smul (c : ℝ) (q : SplitQuaternion) : SplitQuaternion :=
  ⟨c * q.w, c * q.x, c * q.y, c * q.z⟩

/-- The fundamental nilpotent split quaternion `N = i - j`. -/
def N_nil : SplitQuaternion := ⟨0, 1, -1, 0⟩

/-- Recursive finite product representing finite-stage transport. -/
def sq_recursive_prod (t : ℕ → ℝ) (N : SplitQuaternion) : ℕ → SplitQuaternion
  | 0 => 1
  | n + 1 => sq_recursive_prod t N n * (1 + sq_smul (t n) N)

/-- Recursive finite sum representing parameter accumulation. -/
def recursive_sum (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => recursive_sum t n + t n

/-- Coordinate-wise convergence for split-quaternion sequences. -/
def sq_tendsto (q : ℕ → SplitQuaternion) (limit : SplitQuaternion) : Prop :=
  Tendsto (fun n => (q n).w) atTop (nhds limit.w) ∧
  Tendsto (fun n => (q n).x) atTop (nhds limit.x) ∧
  Tendsto (fun n => (q n).y) atTop (nhds limit.y) ∧
  Tendsto (fun n => (q n).z) atTop (nhds limit.z)

/-- The normalized sequence of finite products with parameter `T`. -/
noncomputable def sq_finite_prod_seq (T : ℝ) (n : ℕ) : SplitQuaternion :=
  if n = 0 then 1 else sq_recursive_prod (fun _ => T / (n : ℝ)) N_nil n

/-- Algebraic nilpotent truncation `1 + T • (i - j)`. -/
def sq_nilpotent_exp (T : ℝ) : SplitQuaternion :=
  1 + sq_smul T N_nil

/-- Nilpotency of `N = i - j`. -/
theorem N_nil_sq : N_nil * N_nil = 0 := by
  ext <;> simp [N_nil, sqMul, sqZero]

/-- Closed coordinate form of the algebraic nilpotent truncation. -/
theorem sq_nilpotent_exp_eq (T : ℝ) :
    sq_nilpotent_exp T = ⟨1, T, -T, 0⟩ := by
  ext <;> simp [sq_nilpotent_exp, sq_smul, N_nil, sqAdd, sqOne]

/-- Finite-stage product collapse for the concrete nilpotent `N = i - j`. -/
theorem sq_nilpotent_prod_induction_N (t : ℕ → ℝ) (n : ℕ) :
    sq_recursive_prod t N_nil n = 1 + sq_smul (recursive_sum t n) N_nil := by
  induction n with
  | zero =>
    ext <;> simp [sq_recursive_prod, recursive_sum, sq_smul, N_nil, sqAdd, sqOne]
  | succ k ih =>
    unfold sq_recursive_prod recursive_sum
    rw [ih]
    ext <;> simp [sq_smul, N_nil, sqAdd, sqMul, sqOne]
    ring

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

/-- Exact division sum evaluation. -/
lemma recursive_sum_div (T : ℝ) (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    recursive_sum (fun _ => T / (n : ℝ)) n = T := by
  rw [recursive_sum_const]
  field_simp [hn]

/-- Evaluation of the normalized finite product at any positive stage. -/
lemma sq_finite_prod_seq_val (T : ℝ) (n : ℕ) (hn : n > 0) :
    sq_finite_prod_seq T n = ⟨1, T, -T, 0⟩ := by
  unfold sq_finite_prod_seq
  have hn_ne : n ≠ 0 := by linarith
  rw [if_neg hn_ne]
  rw [sq_nilpotent_prod_induction_N]
  have hn_real_ne : (n : ℝ) ≠ 0 := by
    have h_pos : (n : ℝ) > 0 := by positivity
    linarith
  rw [recursive_sum_div T n hn_real_ne]
  ext <;> simp [sq_smul, N_nil, sqAdd, sqOne]

/-- Coordinate-wise limit of the split-quaternion nilpotent finite products. -/
theorem sq_finite_to_infinite_limit (T : ℝ) :
    sq_tendsto (fun n => sq_finite_prod_seq T n) (sq_nilpotent_exp T) := by
  rw [sq_nilpotent_exp_eq]
  unfold sq_tendsto
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_eq : (fun n => (sq_finite_prod_seq T n).w) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      rw [Filter.EventuallyEq, eventually_atTop]
      use 1
      intro n hn
      have hn_gt : n > 0 := by linarith
      rw [sq_finite_prod_seq_val T n hn_gt]
    exact Filter.tendsto_congr' h_eq |>.mpr tendsto_const_nhds
  · have h_eq : (fun n => (sq_finite_prod_seq T n).x) =ᶠ[atTop] (fun _ => T) := by
      rw [Filter.EventuallyEq, eventually_atTop]
      use 1
      intro n hn
      have hn_gt : n > 0 := by linarith
      rw [sq_finite_prod_seq_val T n hn_gt]
    exact Filter.tendsto_congr' h_eq |>.mpr tendsto_const_nhds
  · have h_eq : (fun n => (sq_finite_prod_seq T n).y) =ᶠ[atTop] (fun _ => -T) := by
      rw [Filter.EventuallyEq, eventually_atTop]
      use 1
      intro n hn
      have hn_gt : n > 0 := by linarith
      rw [sq_finite_prod_seq_val T n hn_gt]
    exact Filter.tendsto_congr' h_eq |>.mpr tendsto_const_nhds
  · have h_eq : (fun n => (sq_finite_prod_seq T n).z) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      rw [Filter.EventuallyEq, eventually_atTop]
      use 1
      intro n hn
      have hn_gt : n > 0 := by linarith
      rw [sq_finite_prod_seq_val T n hn_gt]
    exact Filter.tendsto_congr' h_eq |>.mpr tendsto_const_nhds

/--
Debt marker only: the coordinatewise eventually-constant result above does not
prove a general Clifford analytic completion or differential geometric flow.
-/
def split_quaternion_general_analytic_completion_debt : String :=
  "Open: extend the finite nilpotent flow to a genuine analytic completion theorem."

end InfoGeometry.Clifford.SplitQuaternionNilpotentFlow
