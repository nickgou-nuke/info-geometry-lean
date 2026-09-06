import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.NilpotentFiniteProductLimit

set_option autoImplicit false

namespace InfoGeometry.Algebra.NilpotentModularAutomorphism

/- #### BUCKET 1: CLOSED FINITE THEOREMS -/
-- [Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

/-- CLOSED THEOREM 1: Exact nilpotent modular automorphism expansion over a generic non-commutative ring
    for the unit flow (t=1). This confirms the fundamental algebraic factorization 
    (1+N) X (1-N) = X + [N, X] - NXN without assuming commutativity of the ring. -/
theorem nilpotent_automorphism_expansion_unit
  {A : Type*} [Ring A] (N X : A) (_hN : N * N = 0) :
  (1 + N) * X * (1 - N) = X + (N * X - X * N) - N * X * N := by
  calc
    (1 + N) * X * (1 - N) = (1 * X + N * X) * (1 - N) := by rw [add_mul]
    _ = (X + N * X) * (1 - N) := by rw [one_mul]
    _ = X * (1 - N) + N * X * (1 - N) := by rw [add_mul]
    _ = (X * 1 - X * N) + (N * X * 1 - N * X * N) := by rw [mul_sub, mul_sub]
    _ = (X - X * N) + (N * X - N * X * N) := by rw [mul_one, mul_one]
    _ = X + (N * X - X * N) - N * X * N := by abel


def nilpotentDiscreteFlow {A : Type*} [Ring A] (N : A) (t : ℕ) : A :=
  1 + (t : A) * N

theorem discrete_flow_linear {A : Type*} [Ring A] (N : A) (t : ℕ) :
  nilpotentDiscreteFlow N t - 1 = (t : A) * N := by
  unfold nilpotentDiscreteFlow
  abel


/- #### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES -/
-- [Empty.]


/- #### BUCKET 3: OPEN CLOSURE DEBT -/
-- [Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]

/-- CLOSED THEOREM 2: Exact time-parameterized nilpotent modular automorphism expansion.
    For central time parameter `t`, proves
    `(1+tN) X (1-tN) = X + t(NA - AN) - t^2 NAN` over a non-commutative ring. -/
theorem nilpotent_automorphism_expansion_general_time
  {A : Type*} [Ring A] (N X t : A) (h_comm : ∀ Y : A, t * Y = Y * t) (_hN : N * N = 0) :
  (1 + t * N) * X * (1 - t * N) = X + t * (N * X - X * N) - (t * t) * (N * X * N) := by
  have h1 : X * (t * N) = t * (X * N) := by
    calc
      X * (t * N) = (X * t) * N := by rw [mul_assoc]
      _ = (t * X) * N := by rw [←h_comm X]
      _ = t * (X * N) := by rw [mul_assoc]
  have h2 : t * N * X * (t * N) = (t * t) * (N * X * N) := by
    calc
      t * N * X * (t * N) = (t * N) * (X * (t * N)) := by simp [mul_assoc]
      _ = (t * N) * (t * (X * N)) := by rw [h1]
      _ = t * N * t * (X * N) := by simp [mul_assoc]
      _ = t * (N * t) * (X * N) := by simp [mul_assoc]
      _ = t * (t * N) * (X * N) := by rw [show N * t = t * N from (h_comm N).symm]
      _ = (t * t) * (N * X * N) := by simp [mul_assoc]
  have h3 :
      (1 + t * N) * X * (1 - t * N) =
        X - t * (X * N) + (t * (N * X) - (t * t) * (N * X * N)) := by
    calc
      (1 + t * N) * X * (1 - t * N)
          = (X + t * N * X) * (1 - t * N) := by rw [add_mul, one_mul]
      _ = X * (1 - t * N) + (t * N * X) * (1 - t * N) := by rw [add_mul]
      _ = X * 1 - X * (t * N) + ((t * N * X) * 1 - (t * N * X) * (t * N)) := by
            rw [mul_sub, mul_sub]
      _ = X - X * (t * N) + (t * (N * X) - t * N * X * (t * N)) := by simp [mul_assoc]
      _ = X - t * (X * N) + (t * (N * X) - t * N * X * (t * N)) := by rw [h1]
      _ = X - t * (X * N) + (t * (N * X) - (t * t) * (N * X * N)) := by rw [h2]
  rw [h3]
  have h4 :
      X + t * (N * X - X * N) - (t * t) * (N * X * N) =
        X + (t * (N * X) - t * (X * N)) - (t * t) * (N * X * N) := by
    rw [mul_sub]
  rw [h4]
  abel

theorem timed_nilpotent_square
  {A : Type*} [Ring A] (N t : A) (h_comm : ∀ Y : A, t * Y = Y * t) (hN : N * N = 0) :
  (t * N) * (t * N) = 0 := by
  calc
    (t * N) * (t * N) = t * (N * t) * N := by simp [mul_assoc]
    _ = t * (t * N) * N := by rw [show N * t = t * N from (h_comm N).symm]
    _ = (t * t) * (N * N) := by simp [mul_assoc]
    _ = 0 := by rw [hN, mul_zero]

theorem nilpotent_linear_flow_right_inverse
  {A : Type*} [Ring A] (N t : A) (h_comm : ∀ Y : A, t * Y = Y * t) (hN : N * N = 0) :
  (1 + t * N) * (1 - t * N) = 1 := by
  have hsq : (t * N) * (t * N) = 0 := timed_nilpotent_square N t h_comm hN
  calc
    (1 + t * N) * (1 - t * N)
        = 1 * 1 - 1 * (t * N) + ((t * N) * 1 - (t * N) * (t * N)) := by
          rw [add_mul, mul_sub, mul_sub]
    _ = 1 := by rw [one_mul, one_mul, mul_one, hsq]; abel

theorem nilpotent_linear_flow_left_inverse
  {A : Type*} [Ring A] (N t : A) (h_comm : ∀ Y : A, t * Y = Y * t) (hN : N * N = 0) :
  (1 - t * N) * (1 + t * N) = 1 := by
  have hsq : (t * N) * (t * N) = 0 := timed_nilpotent_square N t h_comm hN
  calc
    (1 - t * N) * (1 + t * N)
        = 1 * 1 + 1 * (t * N) - ((t * N) * 1 + (t * N) * (t * N)) := by
          rw [sub_mul, mul_add, mul_add]
    _ = 1 := by rw [one_mul, one_mul, mul_one, hsq]; abel

/--
The normalized finite nilpotent products converge to the algebraic truncation
`1 + T • N` in the eventually-constant nilpotent lane.
This is the honest topological closure available in-repo; no stronger analytic
completion claim is made here.
-/
theorem exponential_flow_truncation
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (N : A) (T : ℝ) (hN : N * N = 0) :
  Filter.Tendsto
    (fun n : ℕ => InfoGeometry.Algebra.NilpotentFiniteProductLimit.finite_prod_seq T N n)
    Filter.atTop
    (nhds (InfoGeometry.Algebra.NilpotentFiniteProductLimit.nilpotent_exp T N)) :=
  InfoGeometry.Algebra.NilpotentFiniteProductLimit.finite_to_infinite_limit T N hN

end InfoGeometry.Algebra.NilpotentModularAutomorphism

