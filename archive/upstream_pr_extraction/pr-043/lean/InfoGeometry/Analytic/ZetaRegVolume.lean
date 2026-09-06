import InfoGeometry.Algebraic.SplitSuperGeometry
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Zeta-regularized supervolume

The analytic objects in this module are functions, series, derivatives, and
theorems.  No trace-class, continuation, or Mellin statement is represented by
an unconnected evidence field.
-/

noncomputable section

namespace InfoGeometry.Analytic

open scoped Topology
open InfoGeometry.Algebraic.SplitSignature

/-- Heat-kernel trace of a real spectral sequence. -/
def heatKernelTrace
    (eigenvalue : ℕ → ℝ)
    (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-t * eigenvalue n)

/-- Signed heat-kernel supertrace for a graded real spectral sequence. -/
def heatKernelSupertrace
    (parity : ℕ → ℤ)
    (eigenvalue : ℕ → ℝ)
    (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ parity n) * Real.exp (-t * eigenvalue n)

/-- Spectral zeta series associated to a complex spectral sequence. -/
def spectralZeta
    (eigenvalue : ℕ → ℂ)
    (s : ℂ) : ℂ :=
  ∑' n : ℕ, eigenvalue n ^ (-s)

/-- Zeta-regularized supervolume `exp (-ζ'(0))`. -/
def zetaRegularizedSupervolume
    (ζ : ℂ → ℂ) : ℂ :=
  Complex.exp (-deriv ζ 0)

/-- A proved derivative value determines the regularized supervolume. -/
theorem zetaRegularizedSupervolume_eq_exp_neg
    {ζ : ℂ → ℂ}
    {d : ℂ}
    (hζ : HasDerivAt ζ d 0) :
    zetaRegularizedSupervolume ζ = Complex.exp (-d) := by
  rw [zetaRegularizedSupervolume, hζ.deriv]

/-- Pointwise equality of zeta functions preserves regularized supervolume. -/
theorem zetaRegularizedSupervolume_congr
    {ζ η : ℂ → ℂ}
    (h : ζ = η) :
    zetaRegularizedSupervolume ζ =
      zetaRegularizedSupervolume η := by
  rw [h]

/-! ## Native analytic relations, without evidence packets -/

/-- Every positive-time heat-kernel term family is summable. -/
def IsTraceClassHeatKernel (term : ℝ → ℕ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → Summable (term t)

/-- A function is the positive-time trace of an explicit heat-kernel family. -/
def IsHeatKernelTrace
    (term : ℝ → ℕ → ℂ)
    (trace : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → trace t = ∑' n, term t n

/-- A proposed model captures the small-positive-time asymptotics of a trace. -/
def HasSmallTimeModel
    (trace model : ℝ → ℂ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => trace t - model t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/--
An analytic continuation is an explicit differentiable complex function
agreeing with a spectral zeta series on a stated domain.
-/
def IsSpectralZetaContinuation
    (eigenvalue : ℕ → ℂ)
    (domain : Set ℂ)
    (continuation : ℂ → ℂ) : Prop :=
  Differentiable ℂ continuation ∧
    ∀ s ∈ domain, continuation s = spectralZeta eigenvalue s

/-- The derivative at zero is derived from the continuation function itself. -/
noncomputable def spectralZetaDerivativeAtZero
    (continuation : ℂ → ℂ) : ℂ :=
  deriv continuation 0

/-- Differentiability supplies the genuine derivative theorem at zero. -/
theorem spectralZeta_hasDerivAt_zero
    {continuation : ℂ → ℂ}
    (hcontinuation : Differentiable ℂ continuation) :
    HasDerivAt continuation
      (spectralZetaDerivativeAtZero continuation) 0 :=
  (hcontinuation 0).hasDerivAt

/-- Zeta regularization of an analytic continuation is its exponential
negative derivative at zero. -/
theorem zetaRegularizedSupervolume_eq_continuation_derivative
    {continuation : ℂ → ℂ}
    (hcontinuation : Differentiable ℂ continuation) :
    zetaRegularizedSupervolume continuation =
      Complex.exp (-spectralZetaDerivativeAtZero continuation) :=
  zetaRegularizedSupervolume_eq_exp_neg
    (spectralZeta_hasDerivAt_zero hcontinuation)

/-- Split-Clifford parity supertrace readout. -/
def splitZetaSupertrace
    (n : ℕ)
    (operator : SplitCliffordEnd n) : ℝ :=
  cliffordSupertrace n operator

/-- Split-Clifford super-Berezinian readout. -/
def splitZetaSuperBerezinian
    (n : ℕ)
    (operator : SplitCliffordEnd n) : ℝ :=
  superBerezinian n operator

/-- Split-Clifford effective action used as the zeta-like potential. -/
def splitZetaLikePotential
    (n : ℕ)
    (operator : SplitCliffordEnd n) : ℝ :=
  superEffectiveAction n operator

/-- Operator-level split-supergeometry owner, without a one-field wrapper. -/
abbrev SplitZetaSupervolumeShadow (n : ℕ) :=
  SplitCliffordEnd n

namespace SplitZetaSupervolumeShadow

/-- Compatibility projection to the unique split-Clifford operator owner. -/
abbrev operator (S : SplitZetaSupervolumeShadow n) : SplitCliffordEnd n :=
  S

/-- Supertrace readout derived from the unique split-Clifford operator owner. -/
def supertraceReadout (S : SplitZetaSupervolumeShadow n) : ℝ :=
  splitZetaSupertrace n S.operator

/-- Super-Berezinian readout derived from the unique operator owner. -/
def superBerezinianReadout (S : SplitZetaSupervolumeShadow n) : ℝ :=
  splitZetaSuperBerezinian n S.operator

/-- Effective-action potential derived from the unique operator owner. -/
def zetaLikePotential (S : SplitZetaSupervolumeShadow n) : ℝ :=
  splitZetaLikePotential n S.operator

@[simp]
theorem supertraceReadout_eq (S : SplitZetaSupervolumeShadow n) :
    S.supertraceReadout = cliffordSupertrace n S.operator :=
  rfl

@[simp]
theorem superBerezinianReadout_eq (S : SplitZetaSupervolumeShadow n) :
    S.superBerezinianReadout = superBerezinian n S.operator :=
  rfl

@[simp]
theorem zetaLikePotential_eq (S : SplitZetaSupervolumeShadow n) :
    S.zetaLikePotential = superEffectiveAction n S.operator :=
  rfl

end SplitZetaSupervolumeShadow

@[simp]
theorem splitZetaLikePotential_eq_neg_log_superBerezinian
    (n : ℕ)
    (operator : SplitCliffordEnd n) :
    splitZetaLikePotential n operator =
      -Real.log (splitZetaSuperBerezinian n operator) :=
  rfl

@[simp]
theorem zetaLikePotential_eq_neg_log_superBerezinian
    (n : ℕ)
    (x : SplitCliffordEnd n) :
    (superEffectiveAction n) x = -Real.log ((superBerezinian n) x) :=
  rfl

end InfoGeometry.Analytic
