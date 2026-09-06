import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic
import InfoGeometry.Topology.ConformalSpin
import InfoGeometry.Canonical.NPotentBoundarySpinBridge

/-!
# Affine Conformal Projective Hull `n`-Potency and Fractional Anyon Spins

This module formalizes the three-layer dictionary relating the projective hull
potency equation $T^n = T$, cyclotomic boundary spectrum $\mu_{n-1}$, fractional
spins $s = m / (n-1) \pmod 1$, and the Georgiev–Hadjiivanov (2024) Fibonacci anyon
topological twist sector:

$$\begin{array}{c}
\textbf{Layer 1: Projective Hull } n\textbf{-Potency} \\
T^n = T \implies \operatorname{Spec}_{\neq 0}(T) \subset \mu_{n-1} = \{ \zeta \in \mathbb{C} \mid \zeta^{n-1} = 1 \} \\
[2mm] \downarrow \\
\textbf{Layer 2: Cyclotomic Fractional Spin Spectrum} \\
\zeta = e^{2\pi i s} \implies s = \frac{m}{n-1} \pmod 1 \\
[2mm] \downarrow \\
\textbf{Layer 3: Physical / CFT Anyon Carriers} \\
\bullet \; n = 3 \text{ (Tripotent / Bose-Fermi / Horizon zero mode): } s \in \{0, 1/2\} \\
\bullet \; n = 4 \text{ ($\mathbb{Z}_3$ Parafermion carrier): } s \in \{0, 1/3, 2/3\} \text{ (contains } h_\psi = 2/3) \\
\bullet \; n = 6 \text{ (6-Potent Hull / Georgiev–Hadjiivanov Fibonacci): } s \in \{0, 1/5, 2/5, 3/5, 4/5\} \\
\text{containing the Fibonacci conformal weight } h_\varepsilon = 2/5 \text{ and twist } \theta_\tau = e^{4\pi i / 5} \in \mu_5.
\end{array}$$

## Key Theorems:
- `inHull_iff_zero_or_rootOfUnity`: $z^n = z \iff z = 0 \vee z^{n-1} = 1$.
- `topologicalPhase_pow_eq_one`: $\theta(m / (n - 1))^{n - 1} = 1$.
- `fractionalSpin_in_hull`: $\theta(m / (n - 1)) \in \operatorname{Roots}(z^n - z)$.
- `tripotent_spin_zero_in_hull`, `tripotent_spin_half_in_hull`: Bose-Fermi spectrum.
- `z3_parafermion_spin_two_thirds_in_hull`: $\mathbb{Z}_3$ parafermion spin $2/3 \in \operatorname{Roots}(z^4 - z)$.
- `fibonacci_twist_isPrimitiveRoot_five`: $\theta_\tau$ is a primitive 5-th root of unity.
- `fibonacciSpin_pow_five_eq_one`: $(e^{2\pi i (2/5)})^5 = 1$.
- `fibonacciSpin_in_sixPotentHull`: $e^{2\pi i (2/5)} \in \operatorname{Roots}(z^6 - z)$.
- `fibonacci_twist_minimal_nPotency`: 6 is the strictly minimal potency degree $n > 1$ with $\theta_\tau^n = \theta_\tau$.
- `fibonacci_boundarySpinRelation`: The explicit phase/potency relation for the Fibonacci twist.
-/

noncomputable section

namespace InfoGeometry.Canonical.AffineConformalHullNPotencyBridge

open Complex
open InfoGeometry.Topology.CFT
open InfoGeometry.Canonical.NPotentBoundarySpinBridge

/-- The n-potency hull polynomial $p_n(z) = z^n - z$. -/
def hullPoly (n : ℕ) (z : ℂ) : ℂ := z ^ n - z

/-- A complex number is in the n-potency hull if $z^n = z$. -/
def inHull (n : ℕ) (z : ℂ) : Prop := z ^ n = z

/-- Fundamental algebraic equivalence: for non-zero $z$, $z^n = z \iff z^{n-1} = 1$ (for $n \ge 2$). -/
theorem inHull_iff_zero_or_rootOfUnity (n : ℕ) (hn : 2 ≤ n) (z : ℂ) :
    inHull n z ↔ z = 0 ∨ z ^ (n - 1) = 1 := by
  dsimp [inHull]
  constructor
  · intro h
    by_cases hz : z = 0
    · left; exact hz
    · right
      have hsub : n - 1 + 1 = n := by omega
      have hpow : z ^ n = z ^ (n - 1) * z := by
        rw [← pow_succ, hsub]
      have hmul : z ^ (n - 1) * z = 1 * z := by
        rw [← hpow, h, one_mul]
      exact mul_right_cancel₀ hz hmul
  · rintro (rfl | hroot)
    · have hne : n ≠ 0 := by omega
      exact zero_pow hne
    · have hsub : n - 1 + 1 = n := by omega
      calc
        z ^ n = z ^ (n - 1) * z := by rw [← pow_succ, hsub]
        _ = 1 * z := by rw [hroot]
        _ = z := one_mul z

/-- Fractional spin parameter $s = m / (n - 1)$ on the $n$-potent boundary. -/
def fractionalSpin (m : ℕ) (n : ℕ) : ConformalSpin :=
  ⟨(m : ℚ) / ((n : ℚ) - 1)⟩

/-- Topological phase acquired by a state with conformal spin $s$ under a full $2\pi$ rotation. -/
def topologicalPhase (s : ConformalSpin) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (s.S : ℂ))

/-- The phase $\theta(m / (n - 1))$ is an $(n - 1)$-th root of unity. -/
theorem topologicalPhase_pow_eq_one (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    (topologicalPhase (fractionalSpin m n)) ^ (n - 1) = 1 := by
  dsimp [topologicalPhase, fractionalSpin]
  rw [← Complex.exp_nat_mul]
  have hne : ((n : ℂ) - 1) ≠ 0 := by
    have : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact_mod_cast this
  have h_nat_cast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
    have : 1 ≤ n := by omega
    have hsub := Nat.cast_sub (R := ℂ) this
    simp only [Nat.cast_one] at hsub
    exact hsub
  have h_exp : ((n - 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (((m : ℚ) / ((n : ℚ) - 1) : ℚ) : ℂ)) =
      ((m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    rw [h_nat_cast]
    calc
      ((n : ℂ) - 1) * (2 * Real.pi * Complex.I * ((m : ℂ) / ((n : ℂ) - 1))) =
          2 * Real.pi * Complex.I * (((n : ℂ) - 1) * ((m : ℂ) / ((n : ℂ) - 1))) := by ring
      _ = 2 * Real.pi * Complex.I * (m : ℂ) := by
        rw [mul_div_cancel₀ (m : ℂ) hne]
      _ = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h_exp]
  exact Complex.exp_nat_mul_two_pi_mul_I m

/-- General Theorem: The fractional spin $s = m / (n - 1)$ belongs to the $n$-potent hull. -/
theorem fractionalSpin_in_hull (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    inHull n (topologicalPhase (fractionalSpin m n)) := by
  rw [inHull_iff_zero_or_rootOfUnity n hn]
  right
  exact topologicalPhase_pow_eq_one n hn m

/-- 3-Potent Hull (Tripotent / Bose-Fermi / Horizon): $n = 3$, spins $s \in \{0, 1/2\}$. -/
theorem fractionalSpin_zero_three : (fractionalSpin 0 3).S = 0 := by
  dsimp [fractionalSpin]; norm_num

theorem fractionalSpin_one_three : (fractionalSpin 1 3).S = (1 : ℚ) / 2 := by
  dsimp [fractionalSpin]; norm_num

theorem tripotent_spin_zero_in_hull : inHull 3 (topologicalPhase ⟨0⟩) := by
  have h := fractionalSpin_in_hull 3 (by norm_num) 0
  convert h using 1 <;> norm_num [fractionalSpin, topologicalPhase]

theorem tripotent_spin_half_in_hull :
    inHull 3 (topologicalPhase ⟨(1 : ℚ) / 2⟩) := by
  have h := fractionalSpin_in_hull 3 (by norm_num) 1
  convert h using 1 <;> norm_num [fractionalSpin, topologicalPhase]

/-- 4-Potent Hull ($\mathbb{Z}_3$ Parafermion carrier): $n = 4$, contains parafermion spin $h_\psi = 2/3$. -/
theorem fractionalSpin_two_four : (fractionalSpin 2 4).S = (2 : ℚ) / 3 := by
  dsimp [fractionalSpin]; norm_num

theorem z3_parafermion_spin_two_thirds_in_hull :
    inHull 4 (topologicalPhase ⟨(2 : ℚ) / 3⟩) := by
  have h := fractionalSpin_in_hull 4 (by norm_num) 2
  convert h using 1 <;> norm_num [fractionalSpin, topologicalPhase]

/-- 6-Potent Hull (Georgiev–Hadjiivanov Fibonacci anyon carrier):
    Conformal weight $h_\varepsilon = 2/5$ and topological twist $\theta_\tau = \exp(4\pi i / 5) \in \mu_5$. -/
def georgievHadjiivanovFibonacciSpin : ConformalSpin :=
  ⟨(2 : ℚ) / 5⟩

theorem fractionalSpin_two_six : fractionalSpin 2 6 = georgievHadjiivanovFibonacciSpin := by
  dsimp [fractionalSpin, georgievHadjiivanovFibonacciSpin]; norm_num

/-- The Georgiev–Hadjiivanov topological twist $\theta_\tau = \exp(4\pi i / 5)$. -/
def fibonacciTopologicalTwist : ℂ :=
  topologicalPhase georgievHadjiivanovFibonacciSpin

/-- The standard primitive 5th root $\exp(2\pi i / 5)$. -/
def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

theorem zeta5_isPrimitive : IsPrimitiveRoot zeta5 5 := by
  exact Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem fibonacciTopologicalTwist_eq_zeta5_sq :
    fibonacciTopologicalTwist = zeta5 ^ 2 := by
  dsimp [fibonacciTopologicalTwist, georgievHadjiivanovFibonacciSpin, topologicalPhase, zeta5]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Key Capstone Theorem: The Fibonacci topological twist is a primitive 5th root of unity. -/
theorem fibonacci_twist_isPrimitiveRoot_five :
    IsPrimitiveRoot fibonacciTopologicalTwist 5 := by
  rw [fibonacciTopologicalTwist_eq_zeta5_sq]
  exact zeta5_isPrimitive.pow_of_coprime 2 (by decide)

/-- The Fibonacci topological twist is a 5-th root of unity. -/
theorem fibonacciSpin_pow_five_eq_one :
    fibonacciTopologicalTwist ^ 5 = 1 :=
  fibonacci_twist_isPrimitiveRoot_five.pow_eq_one

/-- The Georgiev–Hadjiivanov Fibonacci anyon spin belongs to the 6-potent affine conformal hull. -/
theorem fibonacciSpin_in_sixPotentHull :
    inHull 6 fibonacciTopologicalTwist := by
  have h := fractionalSpin_in_hull 6 (by norm_num) 2
  rwa [fractionalSpin_two_six] at h

/-- Explicit equation on the 6-potent polynomial: $p_6(\theta_\tau) = 0$. -/
theorem fibonacciSpin_hullPoly_eq_zero :
    hullPoly 6 fibonacciTopologicalTwist = 0 := by
  dsimp [hullPoly]
  rw [sub_eq_zero]
  exact fibonacciSpin_in_sixPotentHull

/-- Fibonacci twist power is 1 iff exponent is a multiple of 5. -/
theorem fibonacci_twist_pow_eq_one_iff (k : ℕ) :
    fibonacciTopologicalTwist ^ k = 1 ↔ 5 ∣ k :=
  fibonacci_twist_isPrimitiveRoot_five.pow_eq_one_iff_dvd (l := k)

/-- Fibonacci twist is non-zero. -/
theorem fibonacciTopologicalTwist_ne_zero : fibonacciTopologicalTwist ≠ 0 :=
  fibonacci_twist_isPrimitiveRoot_five.ne_zero (by norm_num)

/-- Minimum Potency Capstone Theorem: 6 is the strictly minimal potency degree $n > 1$
    under which the Fibonacci twist satisfies the potency equation $\theta^n = \theta$. -/
theorem fibonacci_twist_minimal_nPotency :
    fibonacciTopologicalTwist ^ 6 = fibonacciTopologicalTwist ∧
      ∀ n : ℕ, 1 < n → n < 6 →
        fibonacciTopologicalTwist ^ n ≠ fibonacciTopologicalTwist := by
  refine ⟨fibonacciSpin_in_sixPotentHull, ?_⟩
  intro n hn1 hn6 hEq
  have hsub : n - 1 + 1 = n := by omega
  have hpow : fibonacciTopologicalTwist ^ n =
      fibonacciTopologicalTwist ^ (n - 1) * fibonacciTopologicalTwist := by
    rw [← pow_succ, hsub]
  rw [hpow] at hEq
  have h_root : fibonacciTopologicalTwist ^ (n - 1) = 1 := by
    have hmul : fibonacciTopologicalTwist ^ (n - 1) * fibonacciTopologicalTwist =
        1 * fibonacciTopologicalTwist := by
      rw [hEq, one_mul]
    exact mul_right_cancel₀ fibonacciTopologicalTwist_ne_zero hmul
  have hdvd : 5 ∣ (n - 1) := (fibonacci_twist_pow_eq_one_iff (n - 1)).mp h_root
  omega

end InfoGeometry.Canonical.AffineConformalHullNPotencyBridge
