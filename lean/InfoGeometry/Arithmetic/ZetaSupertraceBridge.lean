import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.PrimeMajoranaPfaffian
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Order.Filter.Basic

/-!
# Conditional analytic and kernel data

This module records explicit hypotheses for a convergent family of finite
Euler-product readouts and for a zero of a linear operator.  It proves no
convergence, analytic continuation, determinant identity, or zero-spectrum
correspondence on its own.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaSupertraceBridge

open scoped BigOperators

/-- Data witnessing convergence of finite readouts to a supplied function. -/
structure InfiniteEulerProductWitness (s : ℂ) where
  /-- Finite readouts indexed by a cutoff. -/
  finiteEulerProduct : ℕ → ℂ → ℂ

  /-- The target function on the spectral parameter. -/
  zeta : ℂ → ℂ

  /-- The readouts converge to the target value at `s`. -/
  euler_limit :
    Filter.Tendsto
      (fun N => finiteEulerProduct N s)
      Filter.atTop (nhds (zeta s))

  /-- The target function is analytic on the supplied domain. -/
  analyticDomain : Set ℂ
  analytic_continuation :
    AnalyticOnNhd ℂ zeta analyticDomain

/-- Data relating a specified function zero to a nontrivial operator kernel. -/
structure MajoranaZeroModeHypothesis
    (s : ℂ) (H : Type*)
    [AddCommGroup H] [Module ℂ H] where
  /-- The supplied complex-valued function. -/
  zeta : ℂ → ℂ

  /-- The function vanishes at `s`. -/
  is_zeta_zero : zeta s = 0

  /-- The linear operator whose kernel is being tested. -/
  operator : H →ₗ[ℂ] H

  /-- The operator has a nonzero vector in its kernel. -/
  has_zero_mode :
    ∃ v : H, v ≠ 0 ∧ operator v = 0

  /-- The supplied function zero is equivalent to the kernel condition. -/
  zero_correspondence :
    zeta s = 0 ↔ ∃ v : H, v ≠ 0 ∧ operator v = 0

end InfoGeometry.Arithmetic.ZetaSupertraceBridge
