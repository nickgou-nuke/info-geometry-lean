import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Arithmetic.PrimeBitMellinLaplaceBridge

/-!
# Prime-bit Mellin/partition bridge

This is a thin complex-Mellin consumer of the finite prime-bit lattice and
the already-proved Mellin/Laplace character bridge.  The only new content is
the finite mode readout and its finite ungraded `(1 + q)` partition identity.
No infinite Euler product, zeta identification, or analytic continuation is
asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBitMellinPartitionBridge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitLattice
open InfoGeometry.Arithmetic.PrimeBitMellinLaplaceBridge
open scoped BigOperators

private theorem primeBitModeCharacter_eq_cpow
    {L : PrimeBitLattice} (s : ℂ) (ε : PrimeBitState L)
    (p : ℕ) (hp : p ∈ ε.1) :
    Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) = (p : ℂ) ^ (-s) := by
  have hp_prime : Nat.Prime p := L.isPrime p (ε.2 hp)
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp_ne]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ p from le_of_lt hp_pos))
  rw [hlog]
  ring_nf

/-- The finite Mellin character factors into occupied prime-mode characters. -/
theorem primeBitMellin_modeFactorization
    {L : PrimeBitLattice} (s : ℂ) (ε : PrimeBitState L) :
    primeBitMellinCharacter s ε =
      ∏ p ∈ ε.1, (p : ℂ) ^ (-s) := by
  rw [primeBitMellinCharacter_eq_primeBitEnergy_character]
  unfold primeBitEnergy
  have hsum :
      -s * (↑(∑ p ∈ ε.1, Real.log (p : ℝ)) : ℂ) =
        ∑ p ∈ ε.1, (-s * (Real.log (p : ℝ) : ℂ)) := by
    push_cast
    simp [Finset.mul_sum]
  rw [hsum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  exact primeBitModeCharacter_eq_cpow s ε p hp

/-- The finite ungraded fermionic Mellin partition factors over prime modes. -/
theorem primeBitMellin_partitionFactorization
    {L : PrimeBitLattice} [Fintype (PrimeBitState L)] (s : ℂ) :
    (∑ ε : PrimeBitState L, primeBitMellinCharacter s ε) =
      ∏ p ∈ L.primes, (1 + (p : ℂ) ^ (-s)) := by
  classical
  let f : Finset ℕ → ℂ := fun S =>
    if hS : S ⊆ L.primes then
      primeBitMellinCharacter s ⟨S, hS⟩
    else 0
  have hpowerset : ∀ S : Finset ℕ,
      S ∈ L.primes.powerset ↔ S ⊆ L.primes := by
    intro S
    simp
  have hsum :
      (∑ ε : PrimeBitState L, primeBitMellinCharacter s ε) =
        ∑ S ∈ L.primes.powerset, f S := by
    symm
    rw [Finset.sum_subtype L.primes.powerset hpowerset f]
    apply Finset.sum_congr rfl
    intro ε hε
    simp [f, ε.property]
  rw [hsum]
  calc
    (∑ S ∈ L.primes.powerset, f S) =
        ∑ S ∈ L.primes.powerset, ∏ p ∈ S, (p : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [show f S = primeBitMellinCharacter s
          (⟨S, Finset.mem_powerset.mp hS⟩ : PrimeBitState L) by
            simp [f, Finset.mem_powerset.mp hS]]
      simpa using
        (primeBitMellin_modeFactorization s
          (⟨S, Finset.mem_powerset.mp hS⟩ : PrimeBitState L))
    _ = ∏ p ∈ L.primes, (1 + (p : ℂ) ^ (-s)) := by
      simpa using (Finset.prod_one_add (s := L.primes)
        (f := fun p : ℕ => (p : ℂ) ^ (-s))).symm

end InfoGeometry.Arithmetic.PrimeBitMellinPartitionBridge
