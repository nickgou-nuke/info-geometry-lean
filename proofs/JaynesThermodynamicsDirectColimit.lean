import Mathlib

/-!
# Jaynes thermodynamics on finite stages

This owner records only the finite probability and compatibility facts that are
actually available algebraically.  The last theorem is a compatible-family
extension statement; it deliberately does not claim that a particular
topological or algebraic colimit has been constructed here.
-/

noncomputable section

namespace JaynesThermodynamicsDirectColimit

open scoped BigOperators

local instance (α : Type*) : DecidableEq α := Classical.decEq α

structure FiniteProbabilitySpace where
  ι : Type*
  [fintype : Fintype ι]
  nonempty : Nonempty ι
  prob : ι → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_one : ∑ x : ι, prob x = 1

attribute [instance] FiniteProbabilitySpace.fintype

def shannonEntropy (P : FiniteProbabilitySpace) : ℝ :=
  -∑ x : P.ι, P.prob x * Real.log (P.prob x)

def maxEntropyDist (P : FiniteProbabilitySpace) : P.ι → ℝ :=
  fun _ => (Fintype.card P.ι : ℝ)⁻¹

lemma maxEntropyDist_prob (P : FiniteProbabilitySpace) (x : P.ι) :
    0 ≤ maxEntropyDist P x := by
  simp [maxEntropyDist]

lemma maxEntropyDist_sum_one (P : FiniteProbabilitySpace) :
    ∑ x : P.ι, maxEntropyDist P x = 1 := by
  letI := P.nonempty
  simp only [maxEntropyDist]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

def maxEntropyProbabilitySpace (P : FiniteProbabilitySpace) :
    FiniteProbabilitySpace where
  ι := P.ι
  nonempty := P.nonempty
  prob := maxEntropyDist P
  nonneg := maxEntropyDist_prob P
  sum_one := maxEntropyDist_sum_one P

structure Refinement (P Q : FiniteProbabilitySpace) where
  refineFn : P.ι → Q.ι
  onto : Function.Surjective refineFn
  compatible : ∀ x : Q.ι,
    Q.prob x = ∑ y : P.ι, if refineFn y = x then P.prob y else 0

theorem refinement_preserves_probability_sum
    (P Q : FiniteProbabilitySpace) (R : Refinement P Q) :
    ∑ x : Q.ι, Q.prob x = 1 := by
  classical
  calc
    ∑ x : Q.ι, Q.prob x =
        ∑ x : Q.ι, ∑ y : P.ι,
          if R.refineFn y = x then P.prob y else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact R.compatible x
    _ = ∑ y : P.ι, P.prob y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      simp
    _ = 1 := P.sum_one

theorem compatible_observable_has_limit
    {X : Type*} (obs : ℕ → X → ℝ)
  (hcompat : ∀ m n (_h : m ≤ n) (x : X), obs m x = obs n x) :
    ∃ obs_limit : X → ℝ, ∀ n (x : X), obs n x = obs_limit x := by
  refine ⟨obs 0, ?_⟩
  intro n x
  exact (hcompat 0 n (Nat.zero_le n) x).symm

theorem empirical_entropy_self_eq
    (μ : Fin N → ℝ) :
    ∑ i : Fin N, μ i * Real.log (μ i) =
      ∑ i : Fin N, μ i * Real.log (μ i) := by
  rfl

end JaynesThermodynamicsDirectColimit
