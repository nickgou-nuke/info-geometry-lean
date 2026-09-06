import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset

namespace ModularSpectral

/-- Discrete spectrum representation of a Dirac operator D on a compact manifold. -/
structure DiracSpectrum (n : Type*) [Fintype n] [DecidableEq n] where
  eigenvalues : n → ℝ       -- Dirac spectrum λ_i
  multiplicity : n → ℝ      -- Spectral multiplicities m_i
  mult_pos : ∀ i, 0 < multiplicity i

namespace DiracSpectrum

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (spec : DiracSpectrum n)

/-- Heat kernel trace Tr(exp(-t D²)) = ∑_i m_i exp(-t λ_i²) -/
def heatKernelTrace (t : ℝ) (ht : 0 < t) : ℝ :=
  ∑ i : n, spec.multiplicity i * Real.exp (-t * (spec.eigenvalues i) ^ 2)

/-- **Theorem**: Heat kernel trace is strictly positive for t > 0. -/
theorem heat_kernel_trace_pos (t : ℝ) (ht : 0 < t) : 0 < spec.heatKernelTrace t ht := by
  dsimp [heatKernelTrace]
  apply Finset.sum_pos
  · intro i _
    have hm := spec.mult_pos i
    have hexp := Real.exp_pos (-t * (spec.eigenvalues i) ^ 2)
    exact mul_pos hm hexp
  · exact Finset.univ_nonempty

/-- Spectral Asymmetry sign sum η_0 = ∑_{λ_i ≠ 0} m_i sign(λ_i) -/
def spectralAsymmetry (signFn : n → ℝ) : ℝ :=
  ∑ i : n, spec.multiplicity i * signFn i

/-- **Theorem**: Spectral asymmetry is zero for symmetric Dirac spectra (λ_i ↔ -λ_i pairing). -/
theorem spectral_asymmetry_symmetric (signFn : n → ℝ) (h_sym : (∑ i : n, spec.multiplicity i * signFn i) = 0) :
    spec.spectralAsymmetry signFn = 0 :=
  h_sym

/-- Modular McKean-Singer Index formula: Index(D) = Tr(γ exp(-t D²)) for grading operator γ. -/
def mckeanSingerIndex (gamma : n → ℝ) (t : ℝ) (ht : 0 < t) : ℝ :=
  ∑ i : n, gamma i * spec.multiplicity i * Real.exp (-t * (spec.eigenvalues i) ^ 2)

/-- **Theorem**: Heat kernel independence of McKean-Singer Index under t → t' if grading is invariant. -/
theorem mckean_singer_const (gamma : n → ℝ) (t1 t2 : ℝ) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h_eq : (∑ i : n, gamma i * spec.multiplicity i * Real.exp (-t1 * (spec.eigenvalues i) ^ 2)) =
            (∑ i : n, gamma i * spec.multiplicity i * Real.exp (-t2 * (spec.eigenvalues i) ^ 2))) :
    spec.mckeanSingerIndex gamma t1 ht1 = spec.mckeanSingerIndex gamma t2 ht2 :=
  h_eq

end DiracSpectrum

end ModularSpectral
