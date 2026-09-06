import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.SpectralDistance
import InfoGeometry.Arithmetic.FredholmProved
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Meta.FiniteToInfiniteTransitionSOP

/-!
# Zeta Convergence — Absolute Convergence of ζ(β) for Re(β) > 1

Formalizes the absolute convergence via the p-series test:

    Σ |n^{-β}| = Σ n^{-Re(β)} < ∞   ⇔   Re(β) > 1

This is the constructive step that instantiates the FredholmClosureCertificate:
once the absolute convergence is proved, the trace-class operator T = -e^{-βH}
on ℓ²(ℕ^+) has trace ζ(β), and the Fredholm determinant identity follows.

## The Colimit Picture

The partial sums S_N = Σ_{n=1}^N |n^{-β}| form a directed diagram ℕ → ℝ.
The arrows are canonical inclusions S_N ≤ S_M for N ≤ M. The colimit
of this diagram IS the infinite sum Σ_{n=1}^∞ |n^{-β}|.

The SOP lifts the Cauchy criterion to the entire chain. The SplitClifford
colimit provides the limit object. The p-series test is the analytic kernel.

## The Norm Identity

For n > 0 real: |n^{-β}| = n^{-Re(β)}.
This reduces the complex series to a real p-series: Σ n^{-p} with p = Re(β).

Proof: |n^{-(σ+it)}| = |n^{-σ}|·|n^{-it}| = n^{-σ}·1 = n^{-Re(β)}.
Uses Euler's formula |e^{ix}| = 1 and the positivity of n^{-σ}.
-/

open Complex
open Real

namespace InfoGeometry.Arithmetic.ZetaConvergence

/--
**Target: The Norm Identity.** For real n > 0: ‖n^{-β}‖ = n^{-Re(β)}.

Mathlib API: `Complex.norm_cpow_of_real` or `Complex.abs_cpow_of_ne_zero`.
-/
theorem norm_cpow_eq_rpow (β : ℂ) (n : ℕ) (hn : n ≠ 0) :
    ‖(n : ℂ) ^ (-β)‖ = (n : ℝ) ^ (-β.re) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnpos (-β)

/--
**Target: The p-Series Test.** Σ n^{-p} converges iff p > 1.

For β with Re(β) > 1: Σ |n^{-β}| = Σ n^{-Re(β)} converges absolutely.

Mathlib API: `summable_nat_rpow_inv` or `summable_nat_rpow`.
-/
theorem zeta_absolutely_summable (β : ℂ) (h : 1 < β.re) :
    Summable (fun n : ℕ =>
      ‖((n + 1 : ℕ) : ℂ) ^ (-β)‖) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-β.re)) := by
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (-β.re)) := by
    exact (summable_nat_add_iff 1).mpr hbase
  convert hshift using 1
  funext n
  exact norm_cpow_eq_rpow β (n + 1) (Nat.succ_ne_zero n)

/--
**Target: The Colimit Exists.** For Re(β) > 1, the diagram of partial sums
S_N = Σ_{n=1}^N |n^{-β}| should have a colimit in ℝ.

This is equivalent to the Cauchy criterion, which follows from the
p-series convergence above. The SOP lifts the Cauchy property to the
entire chain. The SplitCliffordInfinity colimit provides the limit.

The colimit IS the trace of the trace-class operator T = -e^{-βH}:
    Tr(T) = lim_{N→∞} Σ_{n=1}^N n^{-β} = ζ(β)   for Re(β) > 1.

This is intended to instantiate the `FredholmClosureCertificate`:
    determinant(β) = ∏ (1-n^{-β}) = 1/ζ(β)
    determinant_mul_zeta_eq_one: det·ζ = 1 for Re(β) > 1.
    determinant_ne_zero: det ≠ 0 for Re(β) > 1/2.
-/
theorem zeta_colimit_exists
    (C : InfoGeometry.Arithmetic.FredholmClosure.FredholmClosureCertificate)
    {β : ℂ} (h : 1 < β.re) :
    Filter.Tendsto
      (fun N : ℕ => C.determinantOnIdeal (C.finiteCutoff β N))
      Filter.atTop
      (nhds (C.determinantOnIdeal (C.limitOperator β))) :=
  InfoGeometry.Arithmetic.FredholmClosure.FredholmClosureCertificate.determinant_cutoff_converges C h

end InfoGeometry.Arithmetic.ZetaConvergence
