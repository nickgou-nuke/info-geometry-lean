import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Finite explicit-formula data and arithmetic readouts. -/

open Complex
open Real
open Filter
open Set
open ArithmeticFunction

namespace InfoGeometry.Arithmetic.ExplicitFormula

/-- The Chebyshev ψ function at the finite stage bounded by the natural floor of `x`. -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  (Finset.Icc 1 ⌊x⌋₊).sum (fun n => (Λ n : ℝ))

/-- The smoothed Chebyshev ψ function (ψ₀) which averages at discontinuities.
  ψ₀(x) = ½(ψ(x) + lim_{y→x⁻} ψ(y)) -/
noncomputable def smoothedChebyshevPsi (x : ℝ) : ℝ :=
  if x = (⌊x⌋₊ : ℝ) then
    (chebyshevPsi x + chebyshevPsi (x - 1)) / 2
  else
    chebyshevPsi x

/-! Finite zero-sum readout. -/
noncomputable def zeroSum (x : ℝ) (zeros : Finset ℂ) : ℂ :=
  zeros.sum (fun ρ => (x : ℂ) ^ ρ / ρ)

/-- The constant term in the explicit formula: log(2π) + ½ log(1 - x⁻²) -/
noncomputable def explicitConstantTerm (x : ℝ) : ℝ :=
  Real.log (2 * Real.pi) + (1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ))

/-! The finite explicit-formula proposition. -/
def explicitFormula (x : ℝ) (zeros : Finset ℂ) (_hx : 1 < x) : Prop :=
  (∀ ρ ∈ zeros, 0 < ρ.re ∧ ρ.re < 1) ∧
  ((smoothedChebyshevPsi x : ℂ) =
    (x : ℂ) - zeroSum x zeros - (explicitConstantTerm x : ℂ)) ∧
  (∀ ρ ∈ zeros, star ρ ∈ zeros)

/-! The proposition follows directly from its three component facts. -/
theorem explicitFormula_of_data
    (x : ℝ) (hx : 1 < x)
    (zeros : Finset ℂ)
    (hzeros : ∀ ρ ∈ zeros, 0 < ρ.re ∧ ρ.re < 1)
    (hconj : ∀ ρ ∈ zeros, star ρ ∈ zeros)
    (hformula :
      (smoothedChebyshevPsi x : ℂ) =
        (x : ℂ) - zeroSum x zeros - (explicitConstantTerm x : ℂ)) :
    explicitFormula x zeros hx := by
  exact ⟨hzeros, hformula, hconj⟩

theorem explicitFormula_components
    (x : ℝ) (zeros : Finset ℂ) (hx : 1 < x)
    (h : explicitFormula x zeros hx) :
    (∀ ρ ∈ zeros, 0 < ρ.re ∧ ρ.re < 1) ∧
      ((smoothedChebyshevPsi x : ℂ) =
        (x : ℂ) - zeroSum x zeros - (explicitConstantTerm x : ℂ)) ∧
      (∀ ρ ∈ zeros, star ρ ∈ zeros) := by
  exact h

/-- Finite main-term readout used for the zero-counting placeholder.

The definition intentionally omits the zero-counting and `S(T)` terms; it is
not a formalization of the Riemann--von Mangoldt theorem. -/
noncomputable def N_function (T : ℝ) : ℝ :=
  if T ≤ 0 then 0 else
    (T / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi * Real.exp 1))) + 7 / 8

/-- The argument of ζ on the critical line: S(T) = (1/π) arg ζ(1/2 + iT). -/
noncomputable def S_function (T : ℝ) : ℝ :=
  (1 / Real.pi) * (riemannZeta (1 / 2 + Complex.I * T)).arg

/-- The truncated `N_function` agrees exactly with its declared main term. -/
theorem N_function_main_term_bound (T : ℝ) (hT : T ≥ 2) :
  |N_function T - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8)| ≤ 1 / T := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  rw [N_function]
  simp only [if_neg (not_le.mpr hTpos), sub_self, abs_zero]
  positivity

/-! A zero-free-region implication whose region premise is supplied explicitly. -/
theorem zero_free_region_of_supplied_region :
  (∀ (t : ℝ), riemannZeta (1 + Complex.I * t) ≠ 0) →
  (∃ (c : ℝ), c > 0 ∧
    ∀ (s : ℂ), s.re ≥ 1 - c / Real.log (|s.im| + 2) →
      s.re < 1 → riemannZeta s ≠ 0) →
  ∃ (c : ℝ), c > 0 ∧
    ∀ (s : ℂ), s.re ≥ 1 - c / Real.log (|s.im| + 2) →
      s.re < 1 → riemannZeta s ≠ 0 := by
  intro _ hregion
  exact hregion

/-! A completed-zeta-style function. -/
noncomputable def xi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Complex.exp (-(s / 2) * Complex.log (Real.pi)) *
    Complex.Gamma (s / 2) * riemannZeta s

/-! A finite product equality read back from an explicit hypothesis. -/
theorem hadamard_product_xi_given (s : ℂ) (zeros : Finset ℂ)
    (hproduct :
      xi s =
        xi 0 * zeros.prod (fun ρ => (1 - s / ρ) * Complex.exp (s / ρ))) :
  xi s = xi 0 * zeros.prod (fun ρ => (1 - s / ρ) * Complex.exp (s / ρ)) := by
  exact hproduct

/-! A finite logarithmic-derivative equality read back from an explicit hypothesis. -/
theorem log_derivative_xi_given (s : ℂ) (zeros : Finset ℂ)
    (hlog :
      deriv xi s / xi s =
        zeros.sum (fun ρ => (1 / (s - ρ) + 1 / ρ))) :
  deriv xi s / xi s =
    zeros.sum (fun ρ => 1 / (s - ρ) + 1 / ρ) := by
  exact hlog

end InfoGeometry.Arithmetic.ExplicitFormula
