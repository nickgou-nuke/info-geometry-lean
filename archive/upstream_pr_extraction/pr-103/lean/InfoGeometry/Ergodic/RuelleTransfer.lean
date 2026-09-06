/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace InfoGeometry.Ergodic.RuelleTransfer

noncomputable section

/-!
# Ruelle Transfer Operator & Symbolic Thermodynamics

This module formalizes the thermodynamic formalism of finite Markov chains
for the symbolic dynamics of the Apollonian gas model:
1. **Finite Cylinder Sets**: Words of length n (`BitWord n = Fin n → Bool`).
2. **Shift and Fibers**: Unilateral shift `σ` and its 2 fiber extensions (`extendWord`).
3. **Ruelle Transfer Operator `ℒ_φ`**: Expectation values weighted by thermodynamic potential `φ(y)`.
4. **Dual Perron-Frobenius Operator**: Evolution of Markov probability measures forward in time.
5. **Local Duality**: Exact fiber pairing between observables and measures.
-/

/-- Space of finite binary prefixes (cylinder sets) of length n. -/
def BitWord (n : ℕ) : Type := Fin n → Bool

/-- Unilateral shift operator σ: truncates the first bit, evolving the state forward. -/
def shiftWord {n : ℕ} (w : BitWord (n + 1)) : BitWord n :=
  fun i => w i.succ

/-- Fiber extension constructor: prepends a leading bit to a word.
    Uses `Fin.cases` for clean, type-safe index splitting. -/
def extendWord {n : ℕ} (b : Bool) (x : BitWord n) : BitWord (n + 1) :=
  Fin.cases b x

/-- 🏆 THEOREM 1 (Exact Topological Recovery):
    Applying the unilateral shift σ to a fiber extension recovers the base word.
    Ensures zero information leakage across Markov levels. -/
theorem shift_extend_word {n : ℕ} (b : Bool) (x : BitWord n) :
    shiftWord (extendWord b x) = x := by
  funext i
  unfold shiftWord extendWord
  rw [Fin.cases_succ]

/-- Ruelle transfer operator ℒ_φ acting on an observable `f` (level n+1),
    weighted by potential `φ`. Returns an observable on level n. -/
def ruelleTransfer {n : ℕ} (φ f : BitWord (n + 1) → ℝ) (x : BitWord n) : ℝ :=
  Real.exp (φ (extendWord false x)) * f (extendWord false x) +
  Real.exp (φ (extendWord true x)) * f (extendWord true x)

/-- Dual Perron-Frobenius operator evolving a measure `ν` (level n)
    to level n+1 along the fiber extensions. -/
def dualTransfer {n : ℕ} (φ : BitWord (n + 1) → ℝ) (ν : BitWord n → ℝ) (y : BitWord (n + 1)) : ℝ :=
  Real.exp (φ y) * ν (shiftWord y)

/-! ### Linearity and Operator Algebra -/

/-- 🏆 THEOREM 2: Additive linearity of the Ruelle transfer operator. -/
theorem ruelle_transfer_add {n : ℕ} (φ f₁ f₂ : BitWord (n + 1) → ℝ) (x : BitWord n) :
    ruelleTransfer φ (fun y => f₁ y + f₂ y) x =
    ruelleTransfer φ f₁ x + ruelleTransfer φ f₂ x := by
  unfold ruelleTransfer
  ring

/-- 🏆 THEOREM 3: Scalar multiplicativity of the Ruelle transfer operator. -/
theorem ruelle_transfer_smul {n : ℕ} (φ f : BitWord (n + 1) → ℝ) (c : ℝ) (x : BitWord n) :
    ruelleTransfer φ (fun y => c * f y) x = c * ruelleTransfer φ f x := by
  unfold ruelleTransfer
  ring

/-- 🏆 THEOREM 4: Markov topological property (Unweighted Transfer).
    For potential φ = 0, transfer on the constant function 1 evaluates to the branching factor 2. -/
theorem transfer_markov_unweighted {n : ℕ} (x : BitWord n) :
    ruelleTransfer (fun _ => 0) (fun _ => 1) x = 2 := by
  unfold ruelleTransfer
  simp [Real.exp_zero] ; norm_num

/-! ### Local Duality and Measure Pairing -/

/-- 🏆 THEOREM 5: Exact Local Dual Pairing.
    Integrating `f` against the transfer operator on `x` equals integrating `ν` against
    the dual operator along both fibers `extendWord false x` and `extendWord true x`:
    ℒ_φ(f)(x) * ν(x) = f(0x) * ℒ_φ*(ν)(0x) + f(1x) * ℒ_φ*(ν)(1x). -/
theorem ruelle_dual_symmetry {n : ℕ} (φ f : BitWord (n + 1) → ℝ) (ν : BitWord n → ℝ) (x : BitWord n) :
    ruelleTransfer φ f x * ν x =
    f (extendWord false x) * dualTransfer φ ν (extendWord false x) +
    f (extendWord true x) * dualTransfer φ ν (extendWord true x) := by
  unfold ruelleTransfer dualTransfer
  rw [shift_extend_word false x, shift_extend_word true x]
  ring

end

end InfoGeometry.Ergodic.RuelleTransfer
