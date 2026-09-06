import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable section

namespace FibAnyonRibbonTwist

inductive FibLabel where
| I
| tau
deriving DecidableEq, Fintype

open FibLabel

variable {K : Type*} [CommRing K]

structure FibonacciCyclotomicData (K : Type*) [CommRing K] where
zeta : K
sqrtTau : K
cyclotomic :
zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1 = 0
sqrtTau_sq :
sqrtTau ^ 2 = zeta ^ 2 - zeta ^ 3

lemma zeta_pow_five (D : FibonacciCyclotomicData K) :
D.zeta ^ 5 = -1 := by
  linear_combination (D.zeta + 1) * D.cyclotomic

lemma zeta_pow_ten (D : FibonacciCyclotomicData K) :
D.zeta ^ 10 = 1 := by
  calc
    D.zeta ^ 10 = (D.zeta ^ 5) ^ 2 := by ring
    _ = (-1 : K) ^ 2 := by rw [zeta_pow_five D]
    _ = 1 := by ring

def fusionAllowed : FibLabel → FibLabel → FibLabel → Bool
| I, I, I => true
| I, tau, tau => true
| tau, I, tau => true
| tau, tau, I => true
| tau, tau, tau => true
| _, _, _ => false

def FibR
(D : FibonacciCyclotomicData K) :
FibLabel → FibLabel → FibLabel → K
| I, I, I => 1
| I, tau, tau => 1
| tau, I, tau => 1
| tau, tau, I => D.zeta ^ 6
| tau, tau, tau => D.zeta ^ 3
| _, _, _ => 0

lemma zeta_pow_fourteen_sub_pow_four
(D : FibonacciCyclotomicData K) :
D.zeta ^ 14 - D.zeta ^ 4 = 0 := by
  calc
  D.zeta ^ 14 - D.zeta ^ 4 =
  D.zeta ^ 4 * (D.zeta ^ 10 - 1) := by ring
  _ = D.zeta ^ 4 * (1 - 1) := by rw [zeta_pow_ten D]
  _ = 0 := by ring

lemma zeta_pow_fourteen_eq_pow_four
(D : FibonacciCyclotomicData K) :
D.zeta ^ 14 = D.zeta ^ 4 := by
  linear_combination zeta_pow_fourteen_sub_pow_four D


/--
The topological spin/twist for the Fibonacci anyons.
-/
def FibTwist
    (D : FibonacciCyclotomicData K) :
    FibLabel → K
  | I => 1
  | tau => D.zeta ^ 4

/--
The multiplicative Ribbon Balancing Identity.
-/
def RibbonBalancingIdentity
    (D : FibonacciCyclotomicData K) : Prop :=
  ∀ a b c : FibLabel,
    fusionAllowed a b c = true →
      FibR D a b c * FibR D b a c *
          FibTwist D a * FibTwist D b =
        FibTwist D c

lemma ribbon_tau_tau_vacuum
    (D : FibonacciCyclotomicData K) :
    (D.zeta ^ 6) * (D.zeta ^ 6) *
        (D.zeta ^ 4) * (D.zeta ^ 4) = 1 := by
  have h_ten : D.zeta ^ 10 = 1 := zeta_pow_ten D
  calc
    (D.zeta ^ 6) * (D.zeta ^ 6) * (D.zeta ^ 4) * (D.zeta ^ 4) =
      (D.zeta ^ 10) * (D.zeta ^ 10) := by ring
    _ = 1 * 1 := by rw [h_ten]
    _ = 1 := by ring

lemma ribbon_tau_tau_tau
    (D : FibonacciCyclotomicData K) :
    (D.zeta ^ 3) * (D.zeta ^ 3) *
        (D.zeta ^ 4) * (D.zeta ^ 4) =
      D.zeta ^ 4 := by
  calc
    D.zeta ^ 3 * D.zeta ^ 3 *
          D.zeta ^ 4 * D.zeta ^ 4 =
        D.zeta ^ 14 := by ring
    _ = D.zeta ^ 4 := zeta_pow_fourteen_eq_pow_four D

theorem fib_anyons_ribbon_balancing
    (D : FibonacciCyclotomicData K) :
    RibbonBalancingIdentity D := by
  intro a b c h
  cases a <;> cases b <;> cases c
  all_goals
    simp [fusionAllowed, FibR, FibTwist] at h ⊢
  · exact ribbon_tau_tau_vacuum D
  · exact ribbon_tau_tau_tau D

end FibAnyonRibbonTwist
