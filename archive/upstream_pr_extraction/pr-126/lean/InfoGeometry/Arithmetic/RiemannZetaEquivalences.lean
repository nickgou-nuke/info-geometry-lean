import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic
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

/-! The logarithmic derivative of the completed readout splits into the
algebraic factors and the completed zeta factor.  This is the finite,
pointwise identity needed before introducing any global Hadamard sum. -/

theorem riemannXi_logDeriv_eq
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  unfold riemannXi
  have hsmul : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hfirst : (1 / 2 : ℂ) * s ≠ 0 := mul_ne_zero hsmul hs0
  have hsecond : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero hfirst hsub
  have hpoly : DifferentiableAt ℂ
      (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s := by
    fun_prop
  have hcompleted : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have hprod := logDeriv_mul (f := fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1))
    (g := completedRiemannZeta) s hsecond hΛ hpoly hcompleted
  have hlinear := logDeriv_mul (f := fun z : ℂ => (1 / 2 : ℂ) * z)
    (g := fun z : ℂ => z - 1) s hfirst hsub (by fun_prop) (by fun_prop)
  calc
    logDeriv riemannXi s =
        logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s +
          logDeriv completedRiemannZeta s := by
      change logDeriv (fun z : ℂ =>
        (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z) s = _
      exact hprod
    _ = 1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
      have hshift : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
        rw [logDeriv_apply]
        have hd : deriv (fun z : ℂ => z - 1) s = 1 := by
          simpa using (hasDerivAt_id s).sub_const (1 : ℂ)
        rw [hd]
      rw [hlinear, logDeriv_const_mul _ _ hsmul, logDeriv_id', hshift]

/-! Native archimedean logarithmic derivative. -/

theorem logDeriv_Gammaℝ_eq
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -((1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  have hGammaℝ : Complex.Gammaℝ = fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z
    exact Complex.Gammaℝ_def z
  rw [hGammaℝ]
  have hhalf : 0 < (s / 2).re := by
    norm_num [Complex.div_re]
    linarith
  have hGamma : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hhalf
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    have hh := hhalf
    rw [h] at hh
    norm_num at hh
    exact (not_lt_of_ge (Nat.cast_nonneg m) hh)
  have hpowDiff : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    apply (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
    exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcompDiff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    hGammaDiff.comp s (by fun_prop)
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hmul := logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Complex.Gamma (z / 2)) s hpow hGamma hpowDiff hcompDiff
  have hpowReadout : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -((1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)) := by
    rw [logDeriv_apply]
    have hderiv := Complex.deriv_const_cpow
      (f := fun z : ℂ => -z / 2) (x := s) (by fun_prop) (Real.pi : ℂ)
    rw [hderiv]
    have hd : deriv (fun z : ℂ => -z / 2) s = -(1 / 2 : ℂ) := by
      convert ((hasDerivAt_id s).neg.div_const (2 : ℂ)).deriv using 1 <;> norm_num
    rw [hd]
    field_simp [hpow]
  have hcompReadout : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
      (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    have hcomp := logDeriv_comp (f := Complex.Gamma)
      (g := fun z : ℂ => z / 2) (x := s) hGammaDiff (by fun_prop)
    rw [show logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
        logDeriv Complex.Gamma (s / 2) *
          deriv (fun z : ℂ => z / 2) s by
      simpa only [Function.comp_apply] using hcomp]
    rw [Complex.digamma_def]
    have hd : deriv (fun z : ℂ => z / 2) s = (1 / 2 : ℂ) := by
      simpa using ((hasDerivAt_id s).div_const (2 : ℂ)).deriv
    rw [hd]
    ring
  rw [hmul, hpowReadout, hcompReadout]

/-! The completed factorization can be differentiated on the absolute
convergence half-plane.  The local equality is used through an eventual
equality, so this theorem does not extend the Dirichlet-series formula past
its genuine domain of convergence. -/

theorem completedRiemannZeta_logDeriv_eq_product
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hΓ : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hcompleted : completedRiemannZeta s =
      riemannZeta s * Complex.Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs0
    exact (eq_div_iff hΓ).mp h |>.symm
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hζDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hΓDiff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    rw [show Complex.Gammaℝ = fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) by
        funext z
        exact Complex.Gammaℝ_def z]
    have hhalf : 0 < (s / 2).re := by
      norm_num [Complex.div_re]
      linarith
    have hGammaDiff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have hh := hhalf
      rw [hm] at hh
      norm_num at hh
      exact (not_lt_of_ge (Nat.cast_nonneg m) hh)
    have hpowDiff : DifferentiableAt ℂ
        (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
      apply (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)
    exact hpowDiff.mul (hGammaDiff.comp s (by fun_prop))
  have hprod := logDeriv_mul (f := riemannZeta)
    (g := Complex.Gammaℝ) s hζ hΓ hζDiff hΓDiff
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : ∀ᶠ z in nhds s,
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hΓz : Complex.Gammaℝ z ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hz)
    have hdef := riemannZeta_def_of_ne_zero hz0
    exact (eq_div_iff hΓz).mp hdef |>.symm
  have hderiv : deriv completedRiemannZeta s =
      deriv (fun z : ℂ => riemannZeta z * Complex.Gammaℝ z) s :=
    Filter.EventuallyEq.deriv_eq heq
  calc
    logDeriv completedRiemannZeta s =
        logDeriv (fun z : ℂ => riemannZeta z * Complex.Gammaℝ z) s := by
      rw [logDeriv_apply, logDeriv_apply, hderiv, hcompleted]
    _ = logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s := hprod

theorem completedRiemannZeta_logDeriv_eq
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv riemannZeta s -
        ((1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  rw [completedRiemannZeta_logDeriv_eq_product hs, logDeriv_Gammaℝ_eq
    (zero_lt_one.trans hs)]
  ring

/-! The concrete `riemannXi` readout inherits the differentiability domain of
the completed zeta factor.  The removable behavior at `0` and `1` is a
separate analytic owner obligation; no extension across those points is
claimed here. -/

theorem differentiableAt_riemannXi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ riemannXi s := by
  have hζ : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  unfold riemannXi
  fun_prop

/-- The concrete completed `riemannXi` readout is nonzero on the absolute
convergence half-plane.  This supplies a genuine nontrivial witness for
constructors that consume the actual completed function; it makes no claim
about zeros in the critical strip. -/
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hZeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hcompleted : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs0
    exact (eq_div_iff hGamma).mp h |>.symm
  unfold riemannXi
  rw [hcompleted]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1')
    (mul_ne_zero hZeta hGamma)

/-- Symmetry-adapted coordinate `z = s - 1/2`. -/
def toSymmetryAdapted (s : ℂ) : ℂ :=
  s - (1 / 2 : ℂ)

/-- Recovery of `s` from `z`. -/
def fromSymmetryAdapted (z : ℂ) : ℂ :=
  z + (1 / 2 : ℂ)

theorem fromSymmetryAdapted_toSymmetryAdapted (s : ℂ) :
    fromSymmetryAdapted (toSymmetryAdapted s) = s := by
  simp [fromSymmetryAdapted, toSymmetryAdapted]

theorem toSymmetryAdapted_fromSymmetryAdapted (z : ℂ) :
    toSymmetryAdapted (fromSymmetryAdapted z) = z := by
  simp [fromSymmetryAdapted, toSymmetryAdapted]

theorem toSymmetryAdapted_one_sub (s : ℂ) :
    toSymmetryAdapted (1 - s) = -toSymmetryAdapted s := by
  simp [toSymmetryAdapted]
  ring

theorem fromSymmetryAdapted_neg (z : ℂ) :
    fromSymmetryAdapted (-z) = 1 - fromSymmetryAdapted z := by
  simp [fromSymmetryAdapted]
  ring

/-- `Ξ(z) = ξ(s(z))`. -/
def symmetryAdaptedXi (z : ℂ) : ℂ :=
  riemannXi (fromSymmetryAdapted z)

theorem symmetryAdaptedXi_toSymmetryAdapted (s : ℂ) :
    symmetryAdaptedXi (toSymmetryAdapted s) = riemannXi s := by
  unfold symmetryAdaptedXi
  rw [fromSymmetryAdapted_toSymmetryAdapted]

theorem differentiableAt_symmetryAdaptedXi {z : ℂ}
    (h0 : fromSymmetryAdapted z ≠ 0)
    (h1 : fromSymmetryAdapted z ≠ 1) :
    DifferentiableAt ℂ symmetryAdaptedXi z := by
  unfold symmetryAdaptedXi
  apply (differentiableAt_riemannXi h0 h1).comp z
  change DifferentiableAt ℂ (fun w : ℂ => w + (1 / 2 : ℂ)) z
  exact (differentiableAt_id (𝕜 := ℂ) (x := z)).add_const (1 / 2 : ℂ)

/-- The completed `riemannXi` readout is invariant under `s ↦ 1 - s`. -/
theorem riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta_one_sub]
  ring

/-- `Ξ` is strictly even: `Ξ(z) = Ξ(-z)`. -/
theorem symmetryAdaptedXi_is_even (z : ℂ) :
    symmetryAdaptedXi z = symmetryAdaptedXi (-z) := by
  unfold symmetryAdaptedXi fromSymmetryAdapted riemannXi
  have h1 : -(z) + (1 / 2 : ℂ) = 1 - (z + (1 / 2 : ℂ)) := by ring
  rw [h1, completedRiemannZeta_one_sub]
  ring

theorem symmetryAdaptedXi_neg (z : ℂ) :
    symmetryAdaptedXi (-z) = symmetryAdaptedXi z := by
  exact (symmetryAdaptedXi_is_even z).symm

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

theorem completedXiFunctionalEquation (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta (1 - s) := by
  exact (completedRiemannZeta_one_sub s).symm

end InfoGeometry.Arithmetic.RiemannZetaEquivalences

end noncomputable section
