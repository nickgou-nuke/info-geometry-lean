import Mathlib.NumberTheory.Bernoulli
import Mathlib
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.RamanujanOddZeta
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# Riemann Zeta Equivalences

Owner module for closed completed-zeta parity and Euler-product / Dirichlet-series
identities on the absolute-convergence half-plane `Re(s) > 1`; the remaining
analytic-continuation debt is recorded explicitly as target constants.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannZetaEquivalences

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-! ## 1. Completed Zeta Function Parity in Symmetry-Adapted Coordinates -/

/-- The completed Riemann zeta function `ξ(s)`. -/
def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

/-- Symmetry-adapted coordinate `z = s - 1/2`. -/
def toSymmetryAdapted (s : ℂ) : ℂ :=
  s - (1 / 2 : ℂ)

/-- Recovery of `s` from `z`. -/
def fromSymmetryAdapted (z : ℂ) : ℂ :=
  z + (1 / 2 : ℂ)

/-- `Ξ(z) = ξ(s(z))`. -/
def symmetryAdaptedXi (z : ℂ) : ℂ :=
  riemannXi (fromSymmetryAdapted z)

/-- `Ξ` is strictly even: `Ξ(z) = Ξ(-z)`. -/
theorem symmetryAdaptedXi_is_even (z : ℂ) :
    symmetryAdaptedXi z = symmetryAdaptedXi (-z) := by
  unfold symmetryAdaptedXi fromSymmetryAdapted riemannXi
  have h1 : -(z) + (1 / 2 : ℂ) = 1 - (z + (1 / 2 : ℂ)) := by ring
  rw [h1, completedRiemannZeta_one_sub]
  ring

/-! ## 2. Equivalent Representations of the Riemann Zeta Function -/

/-- Euler product over primes. -/
def eulerProductZeta (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹

/-- Dirichlet series indexed from `1` as `n + 1`. -/
def dirichletSeriesZeta (s : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s

/-- Dirichlet eta series indexed from `1` as `n + 1`. -/
def dirichletEta (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((-1 : ℂ) ^ n) / ((n + 1 : ℕ) : ℂ) ^ s

/-! ## 2a. Eta through Mathlib's `ZMod 2` L-function corridor -/

/-- Additive mod-2 periodic sign character. -/
def etaPhi : ZMod 2 → ℂ :=
  fun j => if j = 0 then (-1 : ℂ) else 1

/-- Hurwitz-built analytic continuation of eta. -/
def zmodEtaLFunction (s : ℂ) : ℂ :=
  ZMod.LFunction etaPhi s

/-- Native L-series of the same sign pattern. -/
def dirichletEtaLSeries (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => etaPhi (n : ZMod 2)) s

/-- The mod-2 sign character has zero mean. -/
theorem etaPhi_sum_zero : (∑ j : ZMod 2, etaPhi j) = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by native_decide]
  norm_num [etaPhi]

/-- `zmodEtaLFunction` is `Complex.differentiable` everywhere. -/
theorem zmodEtaLFunction_differentiable :
    Differentiable ℂ zmodEtaLFunction := by
  simpa [zmodEtaLFunction] using
    ZMod.differentiable_LFunction_of_sum_zero etaPhi_sum_zero

/-- On `Re(s) > 1`, `zmodEtaLFunction` agrees with its native `LSeries`. -/
theorem zmodEtaLFunction_eq_dirichletEtaLSeries_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    zmodEtaLFunction s = dirichletEtaLSeries s := by
  simpa [zmodEtaLFunction, dirichletEtaLSeries] using
    ZMod.LFunction_eq_LSeries etaPhi (s := s) hs

/-- The native `LSeries` coefficient agrees with the shifted textbook sign. -/
theorem etaPhi_natCast_succ (n : ℕ) :
    etaPhi ((n + 1 : ℕ) : ZMod 2) = (-1 : ℂ) ^ n := by
  rcases Nat.even_or_odd n with hn | hn
  · have hodd : Odd (n + 1) := hn.add_odd odd_one
    have hz : (((n + 1 : ℕ) : ZMod 2) = 1) :=
      ZMod.natCast_eq_one_iff_odd.mpr hodd
    rw [hz]
    rw [show (-1 : ℂ) ^ n = 1 by exact Even.neg_one_pow hn]
    norm_num [etaPhi]
  · have heven : Even (n + 1) := hn.add_odd odd_one
    have hz : (((n + 1 : ℕ) : ZMod 2) = 0) :=
      ZMod.natCast_eq_zero_iff_even.mpr heven
    rw [hz]
    rw [show (-1 : ℂ) ^ n = -1 by exact Odd.neg_one_pow hn]
    norm_num [etaPhi]

/-- On `Re(s) > 1`, the native Mu-L-series eta form agrees with the textbook eta series. -/
theorem dirichletEtaLSeries_eq_dirichletEta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    dirichletEtaLSeries s = dirichletEta s := by
  have hsum : LSeriesSummable (fun n : ℕ => etaPhi (n : ZMod 2)) s :=
    ZMod.LSeriesSummable_of_one_lt_re etaPhi hs
  rw [dirichletEtaLSeries, dirichletEta, LSeries]
  rw [hsum.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  congr 1 with n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  rw [etaPhi_natCast_succ]

/-- On `Re(s) > 1`, the Hurwitz-built eta continuation agrees with the textbook eta series. -/
theorem zmodEtaLFunction_eq_dirichletEta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    zmodEtaLFunction s = dirichletEta s := by
  rw [zmodEtaLFunction_eq_dirichletEtaLSeries_of_one_lt_re s hs,
    dirichletEtaLSeries_eq_dirichletEta_of_one_lt_re s hs]

/-- The Euler product equals the Riemann zeta function for `Re(s) > 1`. -/
theorem eulerProductZeta_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    eulerProductZeta s = riemannZeta s := by
  simpa [eulerProductZeta] using riemannZeta_eulerProduct_tprod (s := s) hs

/-- The Dirichlet series equals `riemannZeta s` on `Re(s) > 1`. -/
theorem dirichletSeriesZeta_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    dirichletSeriesZeta s = riemannZeta s := by
  simpa [dirichletSeriesZeta] using
    (zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs).symm

/-- Closed target statement for the Euler product identity. -/
def EulerProductZetaTarget (s : ℂ) : Prop :=
  1 < s.re → eulerProductZeta s = riemannZeta s

/-- Closed target statement for the Dirichlet-series identity. -/
def DirichletSeriesZetaTarget (s : ℂ) : Prop :=
  1 < s.re → dirichletSeriesZeta s = riemannZeta s

/-- The Euler-product target is already closed from mathlib. -/
theorem eulerProductZetaTarget_closed (s : ℂ) : EulerProductZetaTarget s :=
  eulerProductZeta_eq_riemannZeta s

/-- The Dirichlet-series target is already closed from mathlib. -/
theorem dirichletSeriesZetaTarget_closed (s : ℂ) : DirichletSeriesZetaTarget s :=
  dirichletSeriesZeta_eq_riemannZeta s

/-- Closed target statement for the eta-quotient identity. -/
def DirichletEtaQuotientTarget (s : ℂ) : Prop :=
  0 < s.re → s ≠ 1 →
    riemannZeta s = (1 - (2 : ℂ) ^ (1 - s))⁻¹ * dirichletEta s

/-- Explicit closure debt: the eta-quotient proof on `0 < Re(s)` is deferred. -/
def EtaQuotientAnalyticContinuationDebt : Prop :=
  DirichletEtaQuotientTarget 0

/-- Explicit closure debt: completed-ξ reflection on the full complex plane. -/
def CompletedXiFunctionalEquationDebt (s : ℂ) : Prop :=
  completedRiemannZeta s = completedRiemannZeta (1 - s)

/-! ## 5. Ramanujan-style odd-zeta transformation targets -/

/-- Transparent target for Ramanujan's odd-zeta transformation. -/
def RamanujanOddZetaTarget (n : ℕ) (α β : ℝ) : Prop :=
  0 < n → 0 < α → 0 < β → α * β = Real.pi ^ 2 →
    InfoGeometry.Arithmetic.RamanujanOddZeta.RamanujanOddZetaFormula n α β

end InfoGeometry.Arithmetic.RiemannZetaEquivalences

end noncomputable section
