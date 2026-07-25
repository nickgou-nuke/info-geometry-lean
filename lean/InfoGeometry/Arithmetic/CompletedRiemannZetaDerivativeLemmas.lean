import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# InfoGeometry.Arithmetic.CompletedRiemannZetaDerivativeLemmas

Genuine mathlib-native lemmas for the Riemann zeta derivative layer,
restricted to the open right half-plane `Re(s) > 1`, where the Dirichlet-
series representation converges absolutely.

Every theorem is derived from:
- `Mathlib.NumberTheory.LSeries.RiemannZeta.*`
- `Mathlib.NumberTheory.LSeries.Deriv.LSeries_deriv`
- `Mathlib.NumberTheory.LSeries.Positivity.LSeries_positive`
- repo `RiemannZetaEquivalences.lean`.

No analytic continuation beyond mathlib is claimed.
-/

noncomputable section

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences

namespace InfoGeometry.Arithmetic.CompletedRiemannZetaDerivativeLemmas

/-! ## A. Nonvanishing on `Re(s) > 1` -/

/--
`ζ(s) ≠ 0` for `1 < Re(s)`, from positivity of `LSeries` of positive terms.
-/
theorem riemannZeta_ne_zero_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  have hpos :
      0 < LSeries (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s := by
    have h1 : 0 ≤ (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) := by intro n; positivity
    have h1pos :
        0 < (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) 1 := by norm_num
    have hα :
        LSeries.abscissaOfAbsConv
            (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) < s.re := by
      have hle :
          LSeries.abscissaOfAbsConv
              (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) ≤
            LSeries.abscissaOfAbsConv (fun n : ℕ => (1 : ℂ)) :=
        LSeries.abscissaOfAbsConv_le_of_le_const
          (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s)
          (by
            refine ⟨2, fun n hn ↦ ?_⟩
            dsimp [Function.const]
            norm_num at hn
            simp only [hn]
            positivity)
    have h1e : LSeries.abscissaOfAbsConv (fun n : ℕ => (1 : ℂ)) = 1 := by
      simp [LSeries.abscissaOfAbsConv, abscissaOfAbsConv_const]
    have hlt :
        LSeries.abscissaOfAbsConv
            (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) < (1 : EReal) := by
      refine hle.trans_lt ?_
      simp only [h1e]
      have hlt : (1 : EReal) < s.re := by
        rw [EReal.coe_lt_coe]
        exact hs
      rwa [EReal.coe_lt_coe] at hlt
    exact LT.lt.trans hlt (by
      rw [EReal.coe_lt_coe]
      exact hs)
  have hseries :
      riemannZeta s =
        LSeries (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s := by
    simpa using (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm
  rwa [hseries] at hpos

/--
`Λ(s)` is finite on `Re(s) > 1`; nonzero follows from connective regularity
of the completed zeta there, but that full regularity is not reproved here.
-/
theorem completedRiemannZeta_differentiableAt_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s ≠ 1 := by linarith
  exact differentiableAt_completedZeta hs0 hs1

/-! ## B. Classical zeta derivative on `Re(s) > 1` -/

/--
Genuine derivative formula for `ζ'(s)` on `Re(s) > 1`:
`ζ'(s) = -ζ(s) * Σ log(n+1) / (n+1)^s`.
-/
theorem deriv_riemannZeta_eq_neg_zeta_derivLog_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    deriv riemannZeta s =
      - riemannZeta s * ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℂ) ^ s) := by
  have hz : DifferentiableAt ℂ riemannZeta s := by
    refine differentiableAt_riemannZeta ?_
    intro h
    exact lt_irrefl _ (hs.trans (not_lt.mp h))
  have hseries :
      riemannZeta s =
        LSeries (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s := by
    simpa using (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm
  have hlogsum :
      LSeries.abscissaOfAbsConv
          (LSeries.logMul fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) < s.re := by
    have hle :
        LSeries.abscissaOfAbsConv
            (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) ≤ 1 :=
      LSeries.abscissaOfAbsConv_le_of_le_const
        (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s)
        (by
          refine ⟨2, fun n hn ↦ ?_⟩
          dsimp [Function.const]
          norm_num at hn
          simp only [hn]
          positivity)
    have hlt :
        LSeries.abscissaOfAbsConv
            (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) < s.re :=
      lt_of_le_of_lt hle (by exact_mod_cast hs)
    have hlogconst :
        LSeries.abscissaOfAbsConv
            (LSeries.logMul fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) =
          LSeries.abscissaOfAbsConv
            (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) :=
      LSeries.absicssaOfAbsConv_logMul
        (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s)
    rwa [hlogconst] at hlt
  have hderivL :
      deriv
          (LSeries fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s =
        - LSeries
            (LSeries.logMul fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s :=
    LSeries_deriv hlogsum
  have hlogtsum :
      LSeries
          (LSeries.logMul fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s =
        ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℂ) ^ s) := by
    simp only [LSeries, LSeries.logMul, LSeries.term]
  calc deriv riemannZeta s
      = deriv
          (LSeries fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s :=
        by rw [hseries]
    _ = - LSeries
            (LSeries.logMul fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) s :=
        hderivL
    _ = - ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℂ) ^ s) := by
        rw [hlogtsum]

/--
Wrapper for the classical derivative series formula.
-/
def riemannZetaDeriv (s : ℂ) : ℂ := deriv riemannZeta s

theorem riemannZetaDeriv_formula_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    riemannZetaDeriv s =
      - ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℂ) ^ s) := by
  unfold riemannZetaDeriv
  exact deriv_riemannZeta_eq_neg_zeta_derivLog_of_one_lt_re s hs

/-! ## C. Souriau/zeta Massieu log-derivative on `Re(s) > 1` -/

/--
Genuine log-derivative identity on `Re(s) > 1`:
`(log ◦ ζ(s))' = ζ'(s)/ζ(s)`.
-/
theorem zetaMassieu_deriv_eq_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    deriv (Complex.log ∘ riemannZeta) s =
      deriv riemannZeta s / riemannZeta s := by
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re s hs
  have hd : DifferentiableAt ℂ riemannZeta s := by
    refine differentiableAt_riemannZeta ?_
    intro h
    exact lt_irrefl _ (hs.trans (not_lt.mp h))
  have hlog : HasDerivAt (Complex.log ∘ riemannZeta)
      (deriv riemannZeta s / riemannZeta s) s := by
    have hζderiv : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
      hd.hasDerivAt
    have hlogζ : HasDerivAt Complex.log (1 / riemannZeta s) (riemannZeta s) :=
      HasDerivAt.log hζ
    exact HasDerivAt.comp hlogζ hζderiv
  exact hlog.deriv

end InfoGeometry.Arithmetic.CompletedRiemannZetaDerivativeLemmas
