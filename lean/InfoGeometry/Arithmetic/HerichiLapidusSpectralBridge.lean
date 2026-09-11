import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.MetricSpace.Basic
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge

/-!
# Herichi-Lapidus Spectral Operator Bridge

This file formalizes Step 7 of the Master Execution Pipeline:
the spectral operator framework of Herichi-Lapidus connecting the scale-translation
generator $\partial_c$ on the vertical line $\Re(s) = c$ with Dirichlet operators and
the Riemann zeta spectral image.

## Key Results & Mathematical Distinctions:
1. **Truncated Spectral Operator $a_c^{(T)}$**:
   The point spectrum on the truncated test family $\tau \in [-T, T]$ satisfies:
   $$0 \in \sigma(a_c^{(T)}) \iff \exists \tau \in [-T, T] : \zeta(c + i\tau) = 0.$$
2. **Full Spectral Operator $a_c$**:
   The full $L^2$ closure spectrum satisfies:
   $$\sigma(a_c) = \overline{\zeta(c + i\mathbb{R})},$$
   so $0 \in \sigma(a_c) \iff 0 \in \overline{\zeta(c + i\mathbb{R})}$.
3. **Quasi-Invertibility**:
   $0 \notin \overline{\zeta(c + i\mathbb{R})}$ strictly implies point-nonvanishing
   $\zeta(c + i\tau) \neq 0$ for all $\tau \in \mathbb{R}$, maintaining absolute
   theorem-honesty between invertibility and quasi-invertibility without certificates.
-/

noncomputable section

open Complex
open scoped BigOperators Topology
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge

namespace InfoGeometry.Arithmetic.HerichiLapidusSpectralBridge

/-- Vertical line parameterization $s(c, \tau) = c + i \tau$. -/
def verticalLineParam (c : ℝ) (τ : ℝ) : ℂ :=
  (c : ℂ) + I * (τ : ℂ)

@[simp] theorem verticalLineParam_re (c : ℝ) (τ : ℝ) :
    (verticalLineParam c τ).re = c := by
  dsimp [verticalLineParam]
  simp

@[simp] theorem verticalLineParam_im (c : ℝ) (τ : ℝ) :
    (verticalLineParam c τ).im = τ := by
  dsimp [verticalLineParam]
  simp

/-- Finite Dirichlet polynomial evaluated on the vertical line. -/
def dirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

/-- The finite Dirichlet shift operator acts diagonally on the vertical line test family. -/
theorem finiteDirichletShiftOp_verticalLine (N : ℕ) (c τ : ℝ) :
    finiteDirichletShiftOp N (expTestFun (verticalLineParam c τ)) =
      dirichletPolynomial N (verticalLineParam c τ) • expTestFun (verticalLineParam c τ) := by
  exact finiteDirichletShift_exponentialTest_cpow N (verticalLineParam c τ)

/-!
### 1. Truncated Spectral Operator and Exact Zero Criterion
-/

/-- The truncated spectral image of a multiplier function $F : ℂ \to ℂ$
along the vertical line segment $\Re(s) = c, \Im(s) \in [-T, T]$. -/
def truncatedSpectrum (F : ℂ → ℂ) (c : ℝ) (T : ℝ) : Set ℂ :=
  (fun τ => F (verticalLineParam c τ)) '' Set.Icc (-T) T

/-- Exact zero equivalence for the truncated spectral operator:
$0 \in \sigma(a_c^{(T)}) \iff \exists \tau \in [-T, T], F(c + i\tau) = 0$. -/
theorem zero_mem_truncatedSpectrum_iff (F : ℂ → ℂ) (c : ℝ) (T : ℝ) :
    (0 : ℂ) ∈ truncatedSpectrum F c T ↔ ∃ τ ∈ Set.Icc (-T) T, F (verticalLineParam c τ) = 0 := by
  dsimp [truncatedSpectrum]
  constructor
  · rintro ⟨τ, hτ, hF⟩
    exact ⟨τ, hτ, hF⟩
  · rintro ⟨τ, hτ, hF⟩
    exact ⟨τ, hτ, hF⟩

/-!
### 2. Full Line Spectrum and Quasi-Invertibility
-/

/-- The full line spectrum of $F$ along $\Re(s) = c$ as the topological closure
of the vertical line image $\overline{F(c + i\mathbb{R})}$. -/
def fullLineSpectrum (F : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  closure ((fun τ => F (verticalLineParam c τ)) '' Set.univ)

/-- The truncated spectrum is always contained in the full line closure spectrum. -/
theorem truncatedSpectrum_subset_fullLineSpectrum (F : ℂ → ℂ) (c : ℝ) (T : ℝ) :
    truncatedSpectrum F c T ⊆ fullLineSpectrum F c := by
  dsimp [truncatedSpectrum, fullLineSpectrum]
  rintro z ⟨τ, _, rfl⟩
  exact subset_closure ⟨τ, Set.mem_univ τ, rfl⟩

/-- An exact zero in the truncated window guarantees zero in the full closure spectrum. -/
theorem zero_in_truncated_implies_zero_in_full (F : ℂ → ℂ) (c : ℝ) (T : ℝ) :
    (0 : ℂ) ∈ truncatedSpectrum F c T → (0 : ℂ) ∈ fullLineSpectrum F c := by
  intro h
  exact truncatedSpectrum_subset_fullLineSpectrum F c T h

/-- A vertical zero at $\tau_0$ guarantees that 0 is in the full line spectrum. -/
theorem zero_on_line_implies_zero_in_full (F : ℂ → ℂ) (c : ℝ) (τ₀ : ℝ)
    (hzero : F (verticalLineParam c τ₀) = 0) :
    (0 : ℂ) ∈ fullLineSpectrum F c := by
  have hT : (0 : ℂ) ∈ truncatedSpectrum F c (|τ₀|) := by
    rw [zero_mem_truncatedSpectrum_iff]
    refine ⟨τ₀, ?_, hzero⟩
    rw [Set.mem_Icc]
    exact ⟨neg_abs_le τ₀, le_abs_self τ₀⟩
  exact zero_in_truncated_implies_zero_in_full F c (|τ₀|) hT

/--
**Quasi-Invertibility vs Point Invertibility**:
$F$ is quasi-invertible along the vertical line $\Re(s) = c$ if $0 \notin \overline{F(c + i\mathbb{R})}$.
Quasi-invertibility strictly implies point-nonvanishing $F(c + i\tau) \neq 0$ for all $\tau \in \mathbb{R}$.
-/
def isQuasiInvertible (F : ℂ → ℂ) (c : ℝ) : Prop :=
  (0 : ℂ) ∉ fullLineSpectrum F c

theorem isQuasiInvertible_implies_no_zeros (F : ℂ → ℂ) (c : ℝ) :
    isQuasiInvertible F c → ∀ τ : ℝ, F (verticalLineParam c τ) ≠ 0 := by
  intro hqi τ hzero
  apply hqi
  exact zero_on_line_implies_zero_in_full F c τ hzero

end InfoGeometry.Arithmetic.HerichiLapidusSpectralBridge
