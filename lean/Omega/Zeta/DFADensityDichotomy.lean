import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Zeta.DFADensityDichotomy

/-- DFA density dichotomy arithmetic seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem dfa_vs_prime_count_seeds :
    (2 ^ 4 = 16 ∧ 2 ^ 8 = 256 ∧ 2 ^ 16 = 65536) ∧
    (6 < 16 ∧ 54 < 256 ∧ 6542 < 65536) ∧
    (2 ^ 4 / 4 = 4 ∧ 2 ^ 8 / 8 = 32 ∧ 2 ^ 16 / 16 = 4096) ∧
    (4 < 32 ∧ 32 < 4096) := by
  norm_num

/-- The Fibonacci sequence at index `m + 2` strictly exceeds `m` for every natural `m`.

This arithmetic growth bound is a finite-algebraic input only; it does not establish
non-regularity or non-soficity of any language. -/
theorem fib_gt_linear : ∀ m : ℕ, m < Nat.fib (m + 2)
  | 0 => by norm_num [Nat.fib]
  | n + 1 => by
      have ih := fib_gt_linear n
      have hrec : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
        have h := Nat.fib_add_two (n := n + 1)
        rw [show n + 1 + 2 = n + 3 by omega,
          show n + 1 + 1 = n + 2 by omega] at h
        exact h
      have hpos : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
      rw [show n + 1 + 2 = n + 3 by omega, hrec]
      omega

/-- Paper package: DFA density dichotomy seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem paper_dfa_density_dichotomy_seeds :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) := by
  norm_num [Nat.fib_add_two]

/-- Package wrapper for the DFA density dichotomy seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem paper_dfa_density_dichotomy_package :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) :=
  paper_dfa_density_dichotomy_seeds

/-- Exact paper-facing wrapper for the DFA density dichotomy seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem paper_zeta_syntax_dfa_density_dichotomy :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) :=
  paper_dfa_density_dichotomy_package

end Omega.Zeta.DFADensityDichotomy
