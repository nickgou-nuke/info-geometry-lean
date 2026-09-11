import InfoGeometry.Algebra.CuntzModularAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
import InfoGeometry.Algebra.CuntzConditionalExpectation
import InfoGeometry.Algebra.CuntzModularTreeFlowBridge
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Cuntz Modular Tree Flow Bridge

This file establishes the exact action of the Tomita-Takesaki/gauge modular flow
on the Cuntz tree, bridging the scale-translation geometry with the discrete Cuntz branching.
-/

namespace InfoGeometry.Canonical.CuntzModularTreeFlowBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
open InfoGeometry.Algebra.CuntzConditionalExpectation
open Complex

noncomputable section

theorem modularFlow_cuntzGenerator (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigma n primes t (cuntzS n i) = modularPhase (primes i) t • cuntzS n i :=
  sigma_cuntzS n primes t i

noncomputable def wordPhase (primes : Fin n → ℕ) (t : ℝ) : List (Fin n) → ℂ :=
  InfoGeometry.Algebra.CuntzModularTreeFlowBridge.wordPhase primes t

theorem modularFlow_cuntzWord (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (w : List (Fin n)) :
    sigma n primes t (cuntzWordShift w) = wordPhase primes t w • cuntzWordShift w := by
  exact InfoGeometry.Algebra.CuntzModularTreeFlowBridge.sigma_cuntzWordShift primes t w

theorem modularFlow_cuntzWord_depth (n : ℕ) (p : ℕ) (primes : Fin n → ℕ)
    (h_eq : ∀ i, primes i = p) (t : ℝ) (w : List (Fin n)) :
    sigma n primes t (cuntzWordShift w) = (modularPhase p t) ^ w.length • cuntzWordShift w := by
  rw [modularFlow_cuntzWord]
  have hphase : ∀ v : List (Fin n),
      InfoGeometry.Algebra.CuntzModularTreeFlowBridge.wordPhase primes t v =
        (modularPhase p t) ^ v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons i v ih =>
        simp only [InfoGeometry.Algebra.CuntzModularTreeFlowBridge.wordPhase,
          List.length_cons, h_eq i, ih, pow_succ]
        ring
  change InfoGeometry.Algebra.CuntzModularTreeFlowBridge.wordPhase primes t w •
      cuntzWordShift w = _
  rw [hphase]

/-- A prime-power modular sample is the depth-weighted sample at
    logarithmic time `k * t`.  This is a finite tree identity: no analytic
    functional calculus is used. -/
theorem modularFlow_cuntzWord_prime_power (n p k : ℕ) (t : ℝ)
    (w : List (Fin n)) :
    sigma n (fun _ => p) ((k : ℝ) * t) (cuntzWordShift w) =
      (modularPhase (p ^ k) t) ^ w.length • cuntzWordShift w := by
  rw [modularFlow_cuntzWord_depth n p (fun _ => p) (by intro i; rfl)
    ((k : ℝ) * t) w]
  rw [InfoGeometry.Algebra.CuntzModularTreeFlowBridge.modularPhase_prime_power]

noncomputable def wordPhaseInv (primes : Fin n → ℕ) (t : ℝ) : List (Fin n) → ℂ :=
  InfoGeometry.Algebra.CuntzModularTreeFlowBridge.wordPhaseInv primes t

theorem modularFlow_adjoint (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (w : List (Fin n)) :
    sigma n primes t (cuntzWordShiftDag w) = wordPhaseInv primes t w • cuntzWordShiftDag w := by
  exact InfoGeometry.Algebra.CuntzModularTreeFlowBridge.sigma_cuntzWordShiftDag primes t w

theorem modularFlow_cuntzWordDag_prime_power (n p k : ℕ) (t : ℝ)
    (w : List (Fin n)) :
    sigma n (fun _ => p) ((k : ℝ) * t) (cuntzWordShiftDag w) =
      (modularPhaseInv (p ^ k) t) ^ w.length • cuntzWordShiftDag w := by
  rw [modularFlow_adjoint]
  have hphase :
      wordPhaseInv (fun _ : Fin n => p) ((k : ℝ) * t) w =
        (modularPhaseInv p ((k : ℝ) * t)) ^ w.length := by
    induction w with
    | nil => rfl
    | cons i w ih =>
        change modularPhaseInv p ((k : ℝ) * t) *
            wordPhaseInv (fun _ : Fin n => p) ((k : ℝ) * t) w =
          modularPhaseInv p ((k : ℝ) * t) ^ (List.length w + 1)
        rw [ih, pow_succ, mul_comm]
  rw [hphase]
  rw [InfoGeometry.Algebra.CuntzModularTreeFlowBridge.modularPhaseInv_prime_power]

theorem modularFlow_cylinderProjection (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (w : List (Fin n)) :
    sigma n primes t (cylinderProjection w) = cylinderProjection w := by
  exact InfoGeometry.Algebra.CuntzModularTreeFlowBridge.sigma_cylinderProjection primes t w

theorem modularFlow_cylinderRefinement (n : ℕ) (primes : Fin n → ℕ) (t : ℝ)
    (w : List (Fin n)) :
    sigma n primes t (∑ i : Fin n, cylinderProjection (w ++ [i])) =
      cylinderProjection w := by
  rw [map_sum]
  simp_rw [modularFlow_cylinderProjection]
  exact cylinderProjection_children_sum w

theorem modularFlow_prefixEndomorphism_cylinderProjection
    (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (w : List (Fin n)) :
    sigma n primes t (cuntzPrefixEndomorphism (cylinderProjection w)) =
      cuntzPrefixEndomorphism (cylinderProjection w) := by
  rw [cuntzPrefixEndomorphism_cylinderProjection]
  rw [map_sum]
  simp_rw [modularFlow_cylinderProjection]

theorem cuntzExpectation_modularFlow (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (x : CuntzAlg n) :
    expectation n (sigma n primes t x) = sigma n primes t (expectation n x) := by
  exact InfoGeometry.Algebra.CuntzModularTreeFlowBridge.expectation_sigma_comm primes t x

end
end InfoGeometry.Canonical.CuntzModularTreeFlowBridge
