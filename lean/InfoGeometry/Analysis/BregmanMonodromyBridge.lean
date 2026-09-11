import Mathlib.Analysis.Convex.Gauge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Quantum.Monodromy
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Bregman Monodromy Bridge — Minkowski Gauge × LCFT

Connects convex optimization (Minkowski gauge, self-concordant barriers)
to LCFT (monodromy of the log, nilpotent Jordan blocks).

## Components

1. `minkowskiGauge` — π_y(x) = gauge(K-{y}, x-y)
2. `complexMonodromyErrorShift` — Error(z·e^{2πi}) = Error(z) + 2πiν
3. `monodromyJordanBlock` — J = [[1, 2π]; [0, 1]]
4. `monodromyJordanBlock_pow` — J^n = [[1, 2πn]; [0, 1]] (proved)

## Structural debt

The `Complex.log` monodromy identity log(z·e^{2πi}) = log(z) + 2πi
is a statement about analytic continuation on the universal cover —
not provable on the single-valued principal branch. Requires a Riemann
surface / universal cover setup in mathlib.
-/

noncomputable section

namespace InfoGeometry.Analysis

open Real
open Complex

/--
The Minkowski gauge: the local distance from y to x,
measured as inf{t > 0 | y + t⁻¹(x-y) ∈ K}.
-/
noncomputable def minkowskiGauge {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (K : Set E) (y x : E) : ℝ :=
  gauge ({z : E | z + y ∈ K}) (x - y)

/--
The monodromy error shift: one full winding around the boundary
accumulates 2πiν in the complex log.
-/
noncomputable def complexMonodromyErrorShift (ν : ℝ) (z : ℂ) : ℂ :=
  ν * Complex.log z + (2 * Complex.I * Real.pi * ν)

/--
The nilpotent Jordan block of the monodromy:
J = [[1, 2π]; [0, 1]] acts on the (primary, log-partner) pair.
-/
noncomputable def monodromyJordanBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 2 * π;
     0, 1]

/--
**Theorem**: J^n = [[1, 2πn]; [0, 1]].

The nilpotent (off-diagonal) part accumulates n-fold.
This is the discrete form of the log-monodromy winding.
-/
theorem monodromyJordanBlock_pow (n : ℕ) :
    monodromyJordanBlock ^ n = !![1, (n : ℂ) * (2 * π);
                                   0, 1] := by
  induction' n with n ih
  · ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [monodromyJordanBlock]
  · rw [pow_succ, ih]
    unfold monodromyJordanBlock
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply] <;> ring

/-- The implemented error-shift term is exactly the added `2πiν` contribution. -/
theorem complexMonodromyErrorShift_sub_logTerm (ν : ℝ) (z : ℂ) :
    complexMonodromyErrorShift ν z - ν * Complex.log z =
      2 * Complex.I * Real.pi * ν := by
  unfold complexMonodromyErrorShift
  ring

end InfoGeometry.Analysis
