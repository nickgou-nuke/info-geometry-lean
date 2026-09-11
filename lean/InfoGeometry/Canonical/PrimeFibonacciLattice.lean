import Mathlib.Analysis.SpecificLimits.Fibonacci
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat
open Filter
open scoped goldenRatio Nat.Prime

namespace InfoGeometry.Canonical.PrimeFibonacciLattice

def latticeDimension (n : ℕ) : ℕ := Nat.fib n

theorem latticeDimension_succ_succ (n : ℕ) :
    latticeDimension (n + 2) = latticeDimension (n + 1) + latticeDimension n := by
  simpa [latticeDimension, add_comm, add_left_comm, add_assoc] using
    (Nat.fib_add_two (n := n))

noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

theorem ratio_converges_to_phi :
    Tendsto (fun n ↦ (latticeDimension (n + 1) : ℝ) / latticeDimension n)
      atTop (nhds goldenRatio) := by
  simpa [latticeDimension, goldenRatio] using tendsto_fib_succ_div_fib_atTop

theorem most_irrational_barrier : Irrational goldenRatio := by
  simpa [goldenRatio] using Real.goldenRatio_irrational

theorem latticeDimension_tendsto_atTop : Tendsto latticeDimension atTop atTop := by
  refine Nat.fib_mono.tendsto_atTop_atTop ?_
  intro b
  refine ⟨max b 5, ?_⟩
  have hb : b ≤ max b 5 := le_max_left _ _
  have h5 : 5 ≤ max b 5 := le_max_right _ _
  exact le_trans hb (Nat.le_fib_self h5)

/-- Conditional transport of the prime-counting asymptotic to the Fibonacci lattice.
    This is the honest local theorem available in mathlib: if the prime-counting
    asymptotic is supplied on `ℕ`, then it holds after reindexing by `latticeDimension`. -/
theorem prime_counting_on_lattice
    (h_pnt :
      Tendsto (fun n : ℕ ↦ (π n : ℝ) / ((n : ℝ) / Real.log n)) atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ ↦
        (π (latticeDimension n) : ℝ) / ((latticeDimension n : ℝ) / Real.log (latticeDimension n)))
      atTop (nhds 1) := by
  simpa [latticeDimension] using h_pnt.comp latticeDimension_tendsto_atTop

end InfoGeometry.Canonical.PrimeFibonacciLattice
