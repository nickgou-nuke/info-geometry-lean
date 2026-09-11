import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

/-!
# Finite von Mangoldt Mellin and entropy readouts

This owner formalizes the finite-support part of the von Mangoldt entropy
channel.  It uses the native non-negativity theorem for `Λ` and the
non-negativity of the real exponential.  No infinite Dirichlet series,
analytic logarithmic derivative, or convergence theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteMangoldtEntropyBridge

open scoped BigOperators
open InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

/-- Finite real Mellin readout of the von Mangoldt coefficients. -/
def finiteMangoldtMellin (A : Finset ℕ) (β : ℝ) : ℝ :=
  Finset.sum A (fun n => mangoldtCoefficients n * Real.exp (-β * Real.log n))

theorem finiteMangoldtMellin_nonnegative (A : Finset ℕ) (β : ℝ) :
    0 ≤ finiteMangoldtMellin A β := by
  unfold finiteMangoldtMellin
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    (Real.exp_nonneg _)

/-- A finite Souriau-style entropy readout built from the Mellin energy. -/
def finiteMangoldtEntropy (A : Finset ℕ) (β potential : ℝ) : ℝ :=
  β * finiteMangoldtMellin A β + potential

/-! ## Finite second-law readout -/

/-- With nonnegative inverse temperature and potential, the finite entropy
readout is nonnegative.  This is a finite algebraic statement, not an
infinite Gibbs convergence theorem. -/
theorem finiteMangoldtEntropy_nonnegative
    (A : Finset ℕ) {β potential : ℝ}
    (hβ : 0 ≤ β) (hpotential : 0 ≤ potential) :
    0 ≤ finiteMangoldtEntropy A β potential := by
  unfold finiteMangoldtEntropy
  exact add_nonneg
    (mul_nonneg hβ (finiteMangoldtMellin_nonnegative A β)) hpotential

theorem finiteMangoldtEntropy_master_packet
    (A : Finset ℕ) {β potential : ℝ}
    (hβ : 0 ≤ β) (hpotential : 0 ≤ potential) :
    (0 ≤ finiteMangoldtMellin A β) ∧
    (finiteMangoldtEntropy A β potential =
      β * finiteMangoldtMellin A β + potential) ∧
    (0 ≤ finiteMangoldtEntropy A β potential) := by
  exact ⟨finiteMangoldtMellin_nonnegative A β,
    rfl,
    finiteMangoldtEntropy_nonnegative A hβ hpotential⟩

end InfoGeometry.Arithmetic.FiniteMangoldtEntropyBridge
