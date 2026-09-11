import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.BosonFockReciprocity

open Complex Real ArithmeticFunction

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def primeBosonicFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 / (1 - Complex.cpow (p : ℂ) (-s))

def primeFermionicFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.cpow (p : ℂ) (-s)

def primeSusyPartitionFunction (p : ℕ) (s : ℂ) : ℂ :=
  primeBosonicFactor p s * primeFermionicFactor p s

theorem prime_susy_reciprocity (p : ℕ) (s : ℂ) (h_nz : primeFermionicFactor p s ≠ 0) :
    primeSusyPartitionFunction p s = 1 := by
  unfold primeSusyPartitionFunction primeBosonicFactor primeFermionicFactor at *
  rw [one_div_mul_cancel h_nz]

theorem bosonic_inverse_is_fermionic (p : ℕ) (s : ℂ) (h_nz : primeFermionicFactor p s ≠ 0) :
    primeFermionicFactor p s = (primeBosonicFactor p s)⁻¹ := by
  unfold primeBosonicFactor primeFermionicFactor at *
  rw [inv_div, div_one]
