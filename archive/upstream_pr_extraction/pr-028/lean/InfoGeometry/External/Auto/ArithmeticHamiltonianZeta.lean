import Mathlib.Tactic

/-!
# Arithmetic Hamiltonian and the Zeta Partition Trace

Finite formal model of the dictionary:

* basis state `|n⟩` has energy `E_n = log n`;
* multiplication of integers becomes addition of energies;
* Boltzmann weight `exp (-β log n)` equals the Dirichlet weight `n^(-β)`;
* finite traces are partial sums of these weights.

This file proves finite algebraic/analytic identities.  It does not assert
convergence of the infinite zeta series.
-/

noncomputable section

def arithmeticEnergy (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

def arithmeticBoltzmannWeight (β : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(β * arithmeticEnergy n))

def arithmeticDirichletWeight (β : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-β)

def finiteArithmeticTrace (β : ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum fun k => arithmeticBoltzmannWeight β (k + 1)

def finiteZetaTrace (β : ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum fun k => arithmeticDirichletWeight β (k + 1)

theorem arithmeticEnergy_one :
    arithmeticEnergy 1 = 0 := by
  simp [arithmeticEnergy]

theorem arithmeticEnergy_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    arithmeticEnergy (m * n) = arithmeticEnergy m + arithmeticEnergy n := by
  unfold arithmeticEnergy
  rw [Nat.cast_mul]
  exact Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)

theorem arithmeticEnergy_pow (p k : ℕ) :
    arithmeticEnergy (p ^ k) = (k : ℝ) * arithmeticEnergy p := by
  simp [arithmeticEnergy, Nat.cast_pow, Real.log_pow]

theorem arithmeticBoltzmannWeight_one (β : ℝ) :
    arithmeticBoltzmannWeight β 1 = 1 := by
  simp [arithmeticBoltzmannWeight, arithmeticEnergy_one]

theorem boltzmann_eq_dirichlet (β : ℝ) {n : ℕ} (hn : n ≠ 0) :
    arithmeticBoltzmannWeight β n = arithmeticDirichletWeight β n := by
  unfold arithmeticBoltzmannWeight arithmeticDirichletWeight arithmeticEnergy
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  congr 1
  ring

theorem arithmeticBoltzmannWeight_mul (β : ℝ) (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    arithmeticBoltzmannWeight β (m * n) =
      arithmeticBoltzmannWeight β m * arithmeticBoltzmannWeight β n := by
  unfold arithmeticBoltzmannWeight
  rw [arithmeticEnergy_mul m n hm hn]
  rw [← Real.exp_add]
  congr 1
  ring

theorem finiteArithmeticTrace_succ (β : ℝ) (N : ℕ) :
    finiteArithmeticTrace β (N + 1) =
      finiteArithmeticTrace β N + arithmeticBoltzmannWeight β (N + 1) := by
  simp [finiteArithmeticTrace, Finset.sum_range_succ]

theorem finiteZetaTrace_succ (β : ℝ) (N : ℕ) :
    finiteZetaTrace β (N + 1) =
      finiteZetaTrace β N + arithmeticDirichletWeight β (N + 1) := by
  simp [finiteZetaTrace, Finset.sum_range_succ]

theorem finite_trace_equals_zeta_trace (β : ℝ) (N : ℕ) :
    finiteArithmeticTrace β N = finiteZetaTrace β N := by
  unfold finiteArithmeticTrace finiteZetaTrace
  apply Finset.sum_congr rfl
  intro k hk
  exact boltzmann_eq_dirichlet β (Nat.succ_ne_zero k)

/-- Consolidated finite arithmetic-Hamiltonian package. -/
theorem arithmetic_hamiltonian_zeta_synthesis :
    arithmeticEnergy 1 = 0 ∧
    (∀ m n, m ≠ 0 → n ≠ 0 →
      arithmeticEnergy (m * n) = arithmeticEnergy m + arithmeticEnergy n) ∧
    (∀ (p k : ℕ), arithmeticEnergy (p ^ k) = (k : ℝ) * arithmeticEnergy p) ∧
    (∀ β n, n ≠ 0 → arithmeticBoltzmannWeight β n = arithmeticDirichletWeight β n) ∧
    (∀ β m n, m ≠ 0 → n ≠ 0 →
      arithmeticBoltzmannWeight β (m * n) =
        arithmeticBoltzmannWeight β m * arithmeticBoltzmannWeight β n) ∧
    (∀ β N, finiteArithmeticTrace β (N + 1) =
      finiteArithmeticTrace β N + arithmeticBoltzmannWeight β (N + 1)) ∧
    (∀ β N, finiteArithmeticTrace β N = finiteZetaTrace β N) := by
  exact ⟨arithmeticEnergy_one, arithmeticEnergy_mul, arithmeticEnergy_pow,
    fun β n hn => boltzmann_eq_dirichlet β hn,
    arithmeticBoltzmannWeight_mul, finiteArithmeticTrace_succ,
    finite_trace_equals_zeta_trace⟩

end noncomputable section
