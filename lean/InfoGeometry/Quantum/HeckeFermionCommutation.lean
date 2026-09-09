import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.HeckeFermionCommutation

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def heckeOperator (p : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f (n * p)

def primeShiftOperator (p : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f (n * p)

theorem hecke_prime_shift_commute (p : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    heckeOperator p (primeShiftOperator p f) n =
    primeShiftOperator p (heckeOperator p f) n := by
  unfold heckeOperator primeShiftOperator
  rfl
