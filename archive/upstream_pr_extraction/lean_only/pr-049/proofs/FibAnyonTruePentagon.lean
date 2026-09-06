import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable section

namespace FibAnyonTruePentagon

inductive FibLabel where
| I
| tau
deriving DecidableEq, Fintype

open FibLabel

noncomputable def tau_gr : ℝ :=
(Real.sqrt 5 - 1) / 2

noncomputable def s_gr : ℝ :=
Real.sqrt tau_gr

lemma tau_nonneg : 0 ≤ tau_gr := by
  dsimp [tau_gr]
  have h : (1 : ℝ) ≤ Real.sqrt 5 := by
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  nlinarith

lemma s_sq_eq_tau : s_gr ^ 2 = tau_gr := by
  dsimp [s_gr]
  exact Real.sq_sqrt tau_nonneg

lemma tau_sq_add_tau : tau_gr ^ 2 + tau_gr = 1 := by
  dsimp [tau_gr]
  have h5sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

lemma scalar_s_mul_s : s_gr * s_gr = tau_gr := by
  simpa [pow_two] using s_sq_eq_tau

lemma scalar_tau_mul_tau_add_tau : tau_gr * tau_gr + tau_gr = 1 := by
  simpa [pow_two] using tau_sq_add_tau

lemma scalar_s_mul_s_mul_tau : s_gr * s_gr * tau_gr = tau_gr * tau_gr := by
  rw [scalar_s_mul_s]

lemma scalar_norm : s_gr * s_gr + tau_gr * tau_gr = 1 := by
  rw [scalar_s_mul_s]
  nlinarith [scalar_tau_mul_tau_add_tau]

lemma scalar_cubic : s_gr * s_gr = tau_gr * tau_gr * tau_gr + tau_gr * tau_gr := by
  rw [scalar_s_mul_s]
  calc
    tau_gr = tau_gr * (tau_gr * tau_gr + tau_gr) := by
      rw [scalar_tau_mul_tau_add_tau]
      ring
    _ = tau_gr * tau_gr * tau_gr + tau_gr * tau_gr := by ring

lemma scalar_mixed : s_gr * tau_gr * tau_gr + s_gr * tau_gr = s_gr := by
  calc
    s_gr * tau_gr * tau_gr + s_gr * tau_gr = s_gr * (tau_gr * tau_gr + tau_gr) := by ring
    _ = s_gr := by
      rw [scalar_tau_mul_tau_add_tau]
      ring

/--
`fusionAllowed a b c` is the multiplicity-free Fibonacci fusion coefficient
`Nᶜₐᵦ`, regarded as a Boolean.
-/
def fusionAllowed : FibLabel → FibLabel → FibLabel → Bool
| I, I, I => true
| I, tau, tau => true
| tau, I, tau => true
| tau, tau, I => true
| tau, tau, tau => true
| _, _, _ => false

/--
Index convention:

`FibF a b c d e f = [Fᵃᵇᶜ_d]ₑ_f`.

It is zero unless all four trivalent vertices

`a ⊗ b → e`, `e ⊗ c → d`,
`b ⊗ c → f`, `a ⊗ f → d`

are fusion-admissible.
-/
noncomputable def FibF
(a b c d e f : FibLabel) : ℝ :=
match
fusionAllowed a b e &&
fusionAllowed e c d &&
fusionAllowed b c f &&
fusionAllowed a f d with
| false => 0
| true =>
match a, b, c, d, e, f with
| tau, tau, tau, tau, I, I => tau_gr
| tau, tau, tau, tau, I, tau => s_gr
| tau, tau, tau, tau, tau, I => s_gr
| tau, tau, tau, tau, tau, tau => -tau_gr
| _, _, _, _, _, _ => 1

/--
The three-associator path

`(((a b) c) d) → ((a (b c)) d) → (a ((b c) d)) → (a (b (c d)))`.

The internal channel `z` is contracted over `I` and `tau`.
-/
noncomputable def pentagon_lhs
(a b c d q x y v w : FibLabel) : ℝ :=
FibF a b c y x I *
FibF a I d q y v *
FibF b c d v I w
+
FibF a b c y x tau *
FibF a tau d q y v *
FibF b c d v tau w

/--
The two-associator path

`(((a b) c) d) → ((a b) (c d)) → (a (b (c d)))`.
-/
noncomputable def pentagon_rhs
(a b c d q x y v w : FibLabel) : ℝ :=
FibF x c d q y w *
FibF a b w q x v

theorem fib_anyons_true_pentagon
(a b c d q x y v w : FibLabel) :
pentagon_lhs a b c d q x y v w =
pentagon_rhs a b c d q x y v w := by
  cases a <;>
  cases b <;>
  cases c <;>
  cases d <;>
  cases q <;>
  cases x <;>
  cases y <;>
  cases v <;>
  cases w <;>
  simp [pentagon_lhs, pentagon_rhs, FibF, fusionAllowed] <;>
  nlinarith [
    scalar_s_mul_s,
    scalar_tau_mul_tau_add_tau,
    scalar_s_mul_s_mul_tau,
    scalar_norm,
    scalar_cubic,
    scalar_mixed
  ]

end FibAnyonTruePentagon
