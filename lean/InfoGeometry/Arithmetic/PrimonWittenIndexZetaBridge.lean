import Mathlib
import InfoGeometry.Arithmetic.PrimonGasDirichletAlgebraBridge
import InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

open ArithmeticFunction

/-- Logarithmic real-valued readout attached to a natural-number index. -/
def primonEnergy (n : ℕ) : ℝ := Real.log (n : ℝ)

/-- Real power weight attached to an index and a real parameter. -/
def boltzmannWeight (β : ℝ) (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-β)

/-- The exponential/logarithm identity for positive indices. -/
theorem boltzmannWeight_eq_exp (β : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.exp (-β * primonEnergy n) = boltzmannWeight β n := by
  dsimp [primonEnergy, boltzmannWeight]
  have h_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [mul_comm, <- Real.rpow_def_of_pos h_pos]

/-- Möbius-weighted real power readout. -/
def wittenIndexTerm (β : ℝ) (n : ℕ) : ℝ :=
  (moebius n : ℝ) * boltzmannWeight β n

/-- Multiplicativity of the real power weight. -/
theorem boltzmannWeight_mul (β : ℝ) {a b : ℕ} :
    boltzmannWeight β (a * b) = boltzmannWeight β a * boltzmannWeight β b := by
  dsimp [boltzmannWeight]
  rw [Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

/-- Multiplicativity of the Möbius-weighted readout for coprime indices. -/
theorem wittenIndexTerm_coprime (β : ℝ) {a b : ℕ} (h_cop : a.Coprime b) :
    wittenIndexTerm β (a * b) = wittenIndexTerm β a * wittenIndexTerm β b := by
  dsimp [wittenIndexTerm]
  have h_moeb : (moebius (a * b) : ℝ) = (moebius a : ℝ) * (moebius b : ℝ) := by
    rw [<- Int.cast_mul, isMultiplicative_moebius.map_mul_of_coprime h_cop]
  rw [h_moeb, boltzmannWeight_mul β]
  ring

/-- Möbius is the Dirichlet-convolution inverse of the arithmetic zeta function. -/
theorem moebius_dirichlet_inverse_zeta :
    (moebius : ArithmeticFunction ℤ) * zeta = 1 := by
  exact moebius_mul_coe_zeta

/-- The Möbius-weighted readout at a prime index. -/
theorem wittenIndexTerm_prime (β : ℝ) (p : ℕ) (hp : p.Prime) :
    wittenIndexTerm β p = - Real.rpow (p : ℝ) (-β) := by
  dsimp [wittenIndexTerm, boltzmannWeight]
  rw [moebius_apply_prime hp]
  ring

/-- The readout vanishes at nonsquarefree indices. -/
theorem wittenIndexTerm_zero_of_not_squarefree (β : ℝ) (n : ℕ) (h_sq : ¬ Squarefree n) :
    wittenIndexTerm β n = 0 := by
  dsimp [wittenIndexTerm]
  have h_moeb : moebius n = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h_sq
  rw [h_moeb, Int.cast_zero, zero_mul]

/-- Finite product factorization over a finset of prime indices. -/
theorem wittenIndexTerm_prime_set_prod (β : ℝ) (S : Finset ℕ) (h_primes : ∀ p ∈ S, p.Prime) :
    wittenIndexTerm β (∏ p ∈ S, p) = ∏ p ∈ S, (- Real.rpow (p : ℝ) (-β)) := by
  induction' S using Finset.induction_on with p S hp ih
  · dsimp [wittenIndexTerm, boltzmannWeight]
    have h1 : (moebius 1 : ℝ) = 1 := by rw [moebius_apply_one, Int.cast_one]
    rw [h1, Nat.cast_one, Real.one_rpow, mul_one]
  · rw [Finset.prod_insert hp, Finset.prod_insert hp]
    have hp_prime : p.Prime := h_primes p (Finset.mem_insert_self p S)
    have hS_primes : ∀ q ∈ S, q.Prime := fun q hq => h_primes q (Finset.mem_insert_of_mem hq)
    have h_coprime : p.Coprime (∏ q ∈ S, q) := by
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      have hq_prime : q.Prime := hS_primes q hq
      have h_ne : p ≠ q := fun h_eq => hp (h_eq ▸ hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr h_ne
    rw [wittenIndexTerm_coprime β h_coprime, wittenIndexTerm_prime β p hp_prime, ih hS_primes]

/-- Bundles the preceding finite arithmetic identities. -/
theorem master_primon_witten_index_synthesis
    (β : ℝ) (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 0 < n) (h_sq : ¬ Squarefree n)
    {a b : ℕ} (h_cop : a.Coprime b) (S : Finset ℕ) (h_primes : ∀ q ∈ S, q.Prime) :
    (Real.exp (-β * primonEnergy n) = boltzmannWeight β n) ∧
    (wittenIndexTerm β (a * b) = wittenIndexTerm β a * wittenIndexTerm β b) ∧
    ((moebius : ArithmeticFunction ℤ) * zeta = 1) ∧
    (wittenIndexTerm β p = - Real.rpow (p : ℝ) (-β)) ∧
    (wittenIndexTerm β n = 0) ∧
    (wittenIndexTerm β (∏ q ∈ S, q) = ∏ q ∈ S, (- Real.rpow (q : ℝ) (-β))) := ⟨
  boltzmannWeight_eq_exp β n hn,
  wittenIndexTerm_coprime β h_cop,
  moebius_dirichlet_inverse_zeta,
  wittenIndexTerm_prime β p hp,
  wittenIndexTerm_zero_of_not_squarefree β n h_sq,
  wittenIndexTerm_prime_set_prod β S h_primes
⟩

end InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge
