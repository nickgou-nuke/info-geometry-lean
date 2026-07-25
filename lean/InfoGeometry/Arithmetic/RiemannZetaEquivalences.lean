import Mathlib.NumberTheory.Bernoulli
import Mathlib
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.RamanujanOddZeta
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# Riemann Zeta Equivalences

This file owns the closed completed-zeta parity statement in the
symmetry-adapted coordinate and records the standard analytic equivalences as
explicit proposition targets.

#### BUCKET 1: CLOSED FINITE THEOREMS
`symmetryAdaptedXi_is_even`, derived from mathlib's
`completedRiemannZeta_one_sub`; `zmodEtaLFunction_differentiable` and
`zmodEtaLFunction_eq_dirichletEtaLSeries_of_one_lt_re`, derived from
mathlib's Hurwitz-built `ZMod.LFunction`; and
`zmodEtaLFunction_eq_dirichletEta_of_one_lt_re`, which bridges the native
L-series eta to the textbook shifted eta series.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
The full eta quotient identity against `riemannZeta` on `0 < re s`, and
Ramanujan's odd-zeta transformation.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannZetaEquivalences

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-! ## 1. Completed Zeta Function Parity in Symmetry-Adapted Coordinates -/

/-- The completed Riemann zeta function $\xi(s)$ -/
def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

/-- Symmetry-adapted coordinate $z = s - 1/2$. -/
def toSymmetryAdapted (s : ℂ) : ℂ :=
  s - (1 / 2 : ℂ)

/-- Recovery of s from the symmetry-adapted coordinate z. -/
def fromSymmetryAdapted (z : ℂ) : ℂ :=
  z + (1 / 2 : ℂ)

/-- The Riemann Xi function in symmetry-adapted coordinates. -/
def symmetryAdaptedXi (z : ℂ) : ℂ :=
  riemannXi (fromSymmetryAdapted z)

/-- The functional equation of the Riemann zeta function translates to $\Xi(z) = \Xi(-z)$, proving it is strictly even. -/
theorem symmetryAdaptedXi_is_even (z : ℂ) :
    symmetryAdaptedXi z = symmetryAdaptedXi (-z) := by
  unfold symmetryAdaptedXi fromSymmetryAdapted riemannXi
  have h1 : -(z) + (1 / 2 : ℂ) = 1 - (z + (1 / 2 : ℂ)) := by ring
  rw [h1, completedRiemannZeta_one_sub]
  ring

/-! ## 2. Equivalent Representations of the Riemann Zeta Function -/

/-- The Euler product over primes. -/
def eulerProductZeta (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹

/--
The Dirichlet series representation, indexed from `1` as `n + 1`.
This avoids giving the zero mode any analytic meaning.
-/
def dirichletSeriesZeta (s : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s

/--
The Dirichlet eta function, indexed from `1` as `n + 1`.
The sign is the integer parity `(-1)^n`, not a complex exponent.
-/
def dirichletEta (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((-1 : ℂ) ^ n) / ((n + 1 : ℕ) : ℂ) ^ s

/-! ## 2a. Eta through Mathlib's additive `ZMod 2` L-function corridor -/

/--
The additive mod-2 eta character. This is not a multiplicative Dirichlet
character; it is the periodic function with value `-1` on the even residue and
`1` on the odd residue.
-/
def etaPhi : ZMod 2 → ℂ :=
  fun j => if j = 0 then (-1 : ℂ) else 1

/-- The Hurwitz-built analytic continuation of eta as a `ZMod 2` L-function. -/
def zmodEtaLFunction (s : ℂ) : ℂ :=
  ZMod.LFunction etaPhi s

/--
The native Mathlib L-series form of eta. It is indexed from `1`; the `0` term
is automatically zero in `LSeries.term`.
-/
def dirichletEtaLSeries (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => etaPhi (n : ZMod 2)) s

/-- The mod-2 eta character has zero average, so its L-function has no zeta pole. -/
theorem etaPhi_sum_zero : (∑ j : ZMod 2, etaPhi j) = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by native_decide]
  norm_num [etaPhi]

/-- The `ZMod 2` eta L-function is differentiable everywhere. -/
theorem zmodEtaLFunction_differentiable :
    Differentiable ℂ zmodEtaLFunction := by
  simpa [zmodEtaLFunction] using
    ZMod.differentiable_LFunction_of_sum_zero etaPhi_sum_zero

/--
On the absolute-convergence half-plane, the Hurwitz-built eta L-function agrees
with its native L-series.
-/
theorem zmodEtaLFunction_eq_dirichletEtaLSeries_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    zmodEtaLFunction s = dirichletEtaLSeries s := by
  simpa [zmodEtaLFunction, dirichletEtaLSeries] using
    ZMod.LFunction_eq_LSeries etaPhi (s := s) hs

/-- The native mod-2 eta coefficient matches the shifted textbook sign. -/
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

/-- On `Re(s) > 1`, the native eta L-series is the shifted textbook eta series. -/
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

/--
On `Re(s) > 1`, the Hurwitz-built eta continuation agrees with the textbook
Dirichlet eta series.
-/
theorem zmodEtaLFunction_eq_dirichletEta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    zmodEtaLFunction s = dirichletEta s := by
  rw [zmodEtaLFunction_eq_dirichletEtaLSeries_of_one_lt_re s hs,
    dirichletEtaLSeries_eq_dirichletEta_of_one_lt_re s hs]

/-- The Euler product equals the Riemann zeta function for $\operatorname{Re}(s) > 1$. -/
theorem eulerProductZeta_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    eulerProductZeta s = riemannZeta s := by
  simpa [eulerProductZeta] using riemannZeta_eulerProduct_tprod (s := s) hs

/-- The Dirichlet series equals the Riemann zeta function on `Re(s) > 1`. -/
theorem dirichletSeriesZeta_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    dirichletSeriesZeta s = riemannZeta s := by
  simpa [dirichletSeriesZeta] using
    (zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs).symm

/-- Closed target statement: the Euler product equals zeta on `Re(s) > 1`. -/
def EulerProductZetaTarget (s : ℂ) : Prop :=
  1 < s.re → eulerProductZeta s = riemannZeta s

/-- Closed target statement: the Dirichlet series equals zeta on `Re(s) > 1`. -/
def DirichletSeriesZetaTarget (s : ℂ) : Prop :=
  1 < s.re → dirichletSeriesZeta s = riemannZeta s

/-- The Euler-product target is closed by mathlib's `riemannZeta_eulerProduct_tprod`. -/
theorem eulerProductZetaTarget_closed (s : ℂ) : EulerProductZetaTarget s :=
  eulerProductZeta_eq_riemannZeta s

/-- The Dirichlet-series target is closed by mathlib's zeta Dirichlet-series theorem. -/
theorem dirichletSeriesZetaTarget_closed (s : ℂ) : DirichletSeriesZetaTarget s :=
  dirichletSeriesZeta_eq_riemannZeta s

/-- Target statement: the eta quotient gives zeta off the pole in `Re(s) > 0`. -/
def DirichletEtaQuotientTarget (s : ℂ) : Prop :=\n  0 < s.re → s ≠ 1 → riemannZeta s = (1 - 2 ^ (1 - s))⁻¹ * dirichletEta s\n\nend InfoGeometry.Arithmetic.RiemannZetaEquivalences\n
  0 < s.re → s ≠ 1 → riemannZeta s = (1 - 2 ^ (1 - s))⁻¹ * dirichletEta s

/-! ## 3. Ramanujan's odd-zeta transformation target -/

/--
Transparent target for Ramanujan's odd-zeta transformation. The analytic proof
is not asserted in this file.
-/
def RamanujanOddZetaTarget (n : ℕ) (α β : ℝ) : Prop :=
  0 < n → 0 < α → 0 < β → α * β = Real.pi ^ 2 →
    InfoGeometry.Arithmetic.RamanujanOddZeta.RamanujanOddZetaFormula n α β

end InfoGeometry.Arithmetic.RiemannZetaEquivalences
