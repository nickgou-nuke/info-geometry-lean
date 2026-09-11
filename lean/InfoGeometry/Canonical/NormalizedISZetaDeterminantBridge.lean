import InfoGeometry.Modular.ZetaRegularizedDeterminantBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.TraceFormula.ItakuraSaitoMongeAmpere
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Finite spectral zeta and normalized log-determinants

This owner closes only the finite spectral edge.  It does not introduce an
operator heat trace, analytic continuation, or a Polyakov formula.
-/

noncomputable section

open BigOperators
open Finset
open Matrix

namespace InfoGeometry.Canonical.NormalizedISZetaDeterminantBridge

open InfoGeometry.Modular.Zeta
open InfoGeometry.TraceFormula.ItakuraSaito
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}

/-- The derivative value supplied by the finite spectral zeta owner. -/
def spectralZetaDerivativeAtZero (lam : ι → ℝ) : ℝ :=
  - ∑ i, Real.log (lam i)

omit [DecidableEq ι] in
theorem spectralZetaDerivativeAtZero_eq_deriv
    (lam : ι → ℝ) :
    deriv (spectralZeta lam) 0 = spectralZetaDerivativeAtZero lam := by
  exact (deriv_spectralZeta_zero lam).deriv

omit [DecidableEq ι] in
theorem spectralZetaDerivativeAtZero_eq_neg_log_prod
    (lam : ι → ℝ) (hpos : ∀ i, 0 < lam i) :
    spectralZetaDerivativeAtZero lam = -Real.log (∏ i, lam i) := by
  rw [spectralZetaDerivativeAtZero]
  rw [Real.log_prod (fun i _ => ne_of_gt (hpos i))]

omit [DecidableEq ι] in
theorem spectralZetaDerivativeAtZero_eq_neg_log_zetaDeterminant
    (lam : ι → ℝ) :
    spectralZetaDerivativeAtZero lam =
      -Real.log (zetaDeterminant lam) := by
  rw [spectralZetaDerivativeAtZero, zetaDeterminant]
  rw [Real.log_exp]

/-- Finite zeta regularization agrees with the log-determinant of the
diagonal matrix carrying the same positive spectrum. -/
theorem spectralZetaDerivativeAtZero_eq_neg_log_det_diagonal
    (lam : ι → ℝ) (hpos : ∀ i, 0 < lam i) :
    spectralZetaDerivativeAtZero lam =
      -Real.log (Matrix.det (Matrix.diagonal lam)) := by
  rw [Matrix.det_diagonal]
  exact spectralZetaDerivativeAtZero_eq_neg_log_prod lam hpos

/-! ## The normalized diagonal `BitWord` stage -/

def normalizedSpectralZetaDerivativeAtZero
    (lam : BitWord n → ℝ) : ℝ :=
  (1 / (2 ^ n : ℝ)) * spectralZetaDerivativeAtZero lam

def normalizedDiagonalMongeAmperePotential
    (n : ℕ) (lam : BitWord n → ℝ) : ℝ :=
  (1 / (2 ^ n : ℝ)) *
    mongeAmperePotential n (Matrix.diagonal lam)

theorem normalizedMongeAmpere_eq_normalizedZetaDerivative
    (n : ℕ) (lam : BitWord n → ℝ) (hpos : ∀ i, 0 < lam i) :
    normalizedDiagonalMongeAmperePotential n lam =
      normalizedSpectralZetaDerivativeAtZero lam := by
  unfold normalizedDiagonalMongeAmperePotential
    normalizedSpectralZetaDerivativeAtZero mongeAmperePotential
  rw [spectralZetaDerivativeAtZero_eq_neg_log_det_diagonal lam hpos]

/-! ## Binary bonding of the finite spectral derivative -/

def bondedSpectrum (n : ℕ) (lam : BitWord n → ℝ) :
    BitWord (n + 1) → ℝ :=
  fun w => lam (prefixSucc n w)

theorem spectralZetaDerivativeAtZero_bond_compatible
    (n : ℕ) (lam : BitWord n → ℝ) :
    spectralZetaDerivativeAtZero (bondedSpectrum n lam) =
      2 * spectralZetaDerivativeAtZero lam := by
  unfold spectralZetaDerivativeAtZero bondedSpectrum
  rw [bitword_sum_last_split]
  simp only [prefixSucc_extendSucc]
  simp [Finset.mul_sum, two_mul]

theorem normalizedSpectralZetaDerivativeAtZero_bond_compatible
    (n : ℕ) (lam : BitWord n → ℝ) :
    (1 / (2 ^ (n + 1) : ℝ)) *
        spectralZetaDerivativeAtZero (bondedSpectrum n lam) =
      (1 / (2 ^ n : ℝ)) * spectralZetaDerivativeAtZero lam := by
  rw [spectralZetaDerivativeAtZero_bond_compatible n lam]
  have hpow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [hpow]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

theorem normalizedDiagonalItakuraSaito_eq_trace_plus_zetaDerivative_sub_one
    (n : ℕ) (lam : BitWord n → ℝ) (hpos : ∀ i, 0 < lam i) :
    (1 / (2 ^ n : ℝ)) *
        itakuraSaitoDivergence n (Matrix.diagonal lam) (1 : MatrixStage n) =
      normalizedTrace n (Matrix.diagonal lam) +
        normalizedSpectralZetaDerivativeAtZero lam - 1 := by
  rw [normalized_itakuraSaitoDivergence_eq]
  simp only [inv_one, mul_one]
  have hlog :
      (1 / (2 ^ n : ℝ)) *
          mongeAmperePotential n (Matrix.diagonal lam) =
        normalizedSpectralZetaDerivativeAtZero lam := by
    simpa [normalizedDiagonalMongeAmperePotential] using
      normalizedMongeAmpere_eq_normalizedZetaDerivative n lam hpos
  rw [hlog]


end InfoGeometry.Canonical.NormalizedISZetaDeterminantBridge
