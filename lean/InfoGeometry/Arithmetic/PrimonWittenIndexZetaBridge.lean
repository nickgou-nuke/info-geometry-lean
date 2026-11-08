import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimonGasDirichletAlgebraBridge
import InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

open ArithmeticFunction

/-- **Definition**: The Primon Gas Hamiltonian Energy Functional H(n) = ln(n).
    For a basis state |n⟩ indexed by n ∈ ℕ, H|n⟩ = (ln n)|n⟩. -/
def primonEnergy (n : ℕ) : ℝ := Real.log (n : ℝ)

/-- **Definition**: The Primon Gas Boltzmann Weight w_β(n) = e^(-β * H(n)) = n^(-β). -/
def boltzmannWeight (β : ℝ) (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-β)

/-- **Theorem**: Boltzmann Weight Logarithmic Identity:
    e^(-β * ln n) = n^(-β) for n > 0. -/
theorem boltzmannWeight_eq_exp (β : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.exp (-β * primonEnergy n) = boltzmannWeight β n := by
  dsimp [primonEnergy, boltzmannWeight]
  have h_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [mul_comm, <- Real.rpow_def_of_pos h_pos]

/-- **Definition**: The Primon Gas Witten Index Term w_W(β, n) = μ(n) * n^(-β).
    (-1)^F |n⟩ = μ(n) |n⟩, so <n| (-1)^F e^(-β H) |n> = μ(n) n^(-β). -/
def wittenIndexTerm (β : ℝ) (n : ℕ) : ℝ :=
  (moebius n : ℝ) * boltzmannWeight β n

/-- **Theorem**: Multiplicativity of Boltzmann Weight. -/
theorem boltzmannWeight_mul (β : ℝ) {a b : ℕ} :
    boltzmannWeight β (a * b) = boltzmannWeight β a * boltzmannWeight β b := by
  dsimp [boltzmannWeight]
  rw [Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

/-- **Theorem**: Multiplicativity of Witten Index Term for Coprime Numbers. -/
theorem wittenIndexTerm_coprime (β : ℝ) {a b : ℕ} (h_cop : a.Coprime b) :
    wittenIndexTerm β (a * b) = wittenIndexTerm β a * wittenIndexTerm β b := by
  dsimp [wittenIndexTerm]
  have h_moeb : (moebius (a * b) : ℝ) = (moebius a : ℝ) * (moebius b : ℝ) := by
    rw [<- Int.cast_mul, isMultiplicative_moebius.map_mul_of_coprime h_cop]
  rw [h_moeb, boltzmannWeight_mul β]
  ring

/-- **Theorem**: Dirichlet Convolution Reciprocal Identity for Finite Support / Formal Sums.
    In the Dirichlet convolution ring of arithmetic functions,
    the Dirichlet inverse of the Zeta background state (zeta) is the Möbius parity μ.
    (moebius * zeta) = 1_vacuum. -/
theorem moebius_dirichlet_inverse_zeta :
    (moebius : ArithmeticFunction ℤ) * zeta = 1 := by
  exact moebius_mul_coe_zeta

/-- **Theorem**: Witten Index Identity for Prime State |p⟩.
    For a single prime p, the Witten index term is -p^(-β), reflecting single-fermion parity. -/
theorem wittenIndexTerm_prime (β : ℝ) (p : ℕ) (hp : p.Prime) :
    wittenIndexTerm β p = - Real.rpow (p : ℝ) (-β) := by
  dsimp [wittenIndexTerm, boltzmannWeight]
  rw [moebius_apply_prime hp]
  ring

/-- **Theorem**: Witten Index Zero Locus for Non-Squarefree States.
    If n is not squarefree (has repeated prime factors), the Witten index term vanishes:
    wittenIndexTerm β n = 0, enforcing Pauli Exclusion Principle in the partition sum. -/
theorem wittenIndexTerm_zero_of_not_squarefree (β : ℝ) (n : ℕ) (h_sq : ¬ Squarefree n) :
    wittenIndexTerm β n = 0 := by
  dsimp [wittenIndexTerm]
  have h_moeb : moebius n = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h_sq
  rw [h_moeb, Int.cast_zero, zero_mul]

/-- **Theorem**: Finite Euler Product Factorization of Primon Gas Witten Index.
    For a finite set S of distinct primes, the product state |∏ S| has Witten index term
    equal to the product of individual single-fermion factors:
    w_W(β, ∏_{p ∈ S} p) = ∏_{p ∈ S} (- p^(-β)). -/
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

/-- **Theorem**: Master Primon Witten Index Synthesis.
    Unifies:
    1. Boltzmann weight exponential-log equivalence.
    2. Multiplicativity of Witten Index terms for coprime states.
    3. Möbius Dirichlet inverse of Zeta (Bose-Fermi Vacuum Cancellation).
    4. Single-fermion prime state parity wittenIndexTerm(p) = -p^(-β).
    5. Pauli Exclusion zero locus for non-squarefree states.
    6. Finite Euler product factorization over prime subsets. -/
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
