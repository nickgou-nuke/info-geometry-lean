import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.FermionFockMoebius

open Complex Real ArithmeticFunction

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def primeFermionicFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.cpow (p : ℂ) (-s)

theorem moebius_prime_is_fermionic (p : ℕ) (hp : Nat.Prime p) :
    moebius p = -1 := by
  exact moebius_apply_prime hp

theorem moebius_pauli_exclusion (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 2 ≤ k) :
    moebius (p ^ k) = 0 := by
  have hk0 : k ≠ 0 := by linarith
  rw [moebius_apply_prime_pow hp hk0]
  have : ¬ k = 1 := by linarith
  simp [this]

theorem moebius_vacuum_parity :
    moebius 1 = 1 := by
  exact moebius_apply_one

theorem single_mode_graded_sum (p : ℕ) (s : ℂ) :
    (1 : ℂ) * (1 : ℂ) + (-1 : ℂ) * Complex.cpow (p : ℂ) (-s) =
    primeFermionicFactor p s := by
  unfold primeFermionicFactor
  ring

end
end InfoGeometry.Quantum.FermionFockMoebius
