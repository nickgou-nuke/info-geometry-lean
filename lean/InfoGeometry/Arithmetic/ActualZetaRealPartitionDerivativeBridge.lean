import Mathlib.Analysis.Complex.RealDeriv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

/-!
# Derivative transport for the actual real partition readout

On the real half-line `1 < beta`, the native Dirichlet partition series is
identified with `riemannZeta`.  This owner transports the complex derivative
to the derivative of its real inverse-temperature readout.  It does not
identify that derivative with a Fisher metric or assert an asymptotic.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge

open Filter
open scoped BigOperators
open scoped ComplexOrder
open scoped Topology
open scoped LSeries.notation
open ArithmeticFunction
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge

theorem partitionSeries_partial_sums_tendsto
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun N : ℕ =>
        Finset.sum (Finset.range N)
          (fun n => 1 / ((n + 1 : ℕ) : ℂ) ^ s))
      atTop (𝓝 (partitionSeries s)) := by
  have hsum : Summable (fun n : ℕ =>
      1 / ((n + 1 : ℕ) : ℂ) ^ s) :=
    (summable_partitionSeries_summand s).2 hs
  have hhas : HasSum (fun n : ℕ =>
      1 / ((n + 1 : ℕ) : ℂ) ^ s) (partitionSeries s) := by
    change HasSum (fun n : ℕ =>
      1 / ((n + 1 : ℕ) : ℂ) ^ s)
      (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s)
    exact hsum.hasSum
  exact (hasSum_iff_tendsto_nat_of_summable_norm hsum.norm).mp hhas

theorem realPartitionSeries_deriv_eq_riemannZeta_deriv_re
    {β : ℝ} (hβ : 1 < β) :
    deriv realPartitionSeries β =
      (deriv riemannZeta (β : ℂ)).re := by
  have hlocal : ∀ᶠ x : ℝ in 𝓝 β, 1 < x := by
    exact eventually_gt_nhds hβ
  have heq :
      (fun x : ℝ => realPartitionSeries x) =ᶠ[𝓝 β]
        (fun x : ℝ => (riemannZeta (x : ℂ)).re) := by
    filter_upwards [hlocal] with x hx
    rw [realPartitionSeries_eq_riemannZeta x hx]
  rw [heq.deriv_eq]
  have hz : (β : ℂ) ≠ 1 := by
    exact_mod_cast ne_of_gt hβ
  exact (differentiableAt_riemannZeta hz).hasDerivAt.real_of_complex.deriv

theorem realPartitionSeries_differentiableAt_of_one_lt
    {β : ℝ} (hβ : 1 < β) :
    DifferentiableAt ℝ realPartitionSeries β := by
  have hlocal : ∀ᶠ x : ℝ in 𝓝 β, 1 < x := by
    exact eventually_gt_nhds hβ
  have heq :
      (fun x : ℝ => realPartitionSeries x) =ᶠ[𝓝 β]
        (fun x : ℝ => (riemannZeta (x : ℂ)).re) := by
    filter_upwards [hlocal] with x hx
    rw [realPartitionSeries_eq_riemannZeta x hx]
  apply heq.differentiableAt_iff.2
  have hz : (β : ℂ) ≠ 1 := by
    exact_mod_cast ne_of_gt hβ
  simpa using
    (differentiableAt_riemannZeta hz).hasDerivAt.real_of_complex.differentiableAt

theorem realPartitionSeries_deriv_eq_neg_logDerivative_mul_zeta_re
    {β : ℝ} (hβ : 1 < β) :
    deriv realPartitionSeries β =
      -(actualRiemannZetaLogDerivative (β : ℂ) *
        riemannZeta (β : ℂ)).re := by
  rw [realPartitionSeries_deriv_eq_riemannZeta_deriv_re hβ]
  have hz : riemannZeta (β : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hβ)
  have hcomplex :
      -(actualRiemannZetaLogDerivative (β : ℂ) *
        riemannZeta (β : ℂ)) = deriv riemannZeta (β : ℂ) := by
      unfold actualRiemannZetaLogDerivative
      field_simp [hz]
  exact (congrArg Complex.re hcomplex).symm

theorem realPartitionSeries_deriv_eq_neg_mul_logDerivative_re
    {β : ℝ} (hβ : 1 < β) :
    deriv realPartitionSeries β =
      -(realPartitionSeries β *
        (actualRiemannZetaLogDerivative (β : ℂ)).re) := by
  rw [realPartitionSeries_deriv_eq_neg_logDerivative_mul_zeta_re hβ]
  rw [realPartitionSeries_eq_riemannZeta β hβ]
  have him : (riemannZeta (β : ℂ)).im = 0 :=
    riemannZeta_im_eq_zero_of_one_lt hβ
  simp [Complex.mul_re, him]
  ring

theorem realPartitionSeries_log_deriv_eq_neg_logDerivative_re
    {β : ℝ} (hβ : 1 < β) :
    deriv (fun x : ℝ => Real.log (realPartitionSeries x)) β =
      -(actualRiemannZetaLogDerivative (β : ℂ)).re := by
  rw [deriv.log (realPartitionSeries_differentiableAt_of_one_lt hβ)
    (ne_of_gt (realPartitionSeries_pos β hβ))]
  rw [realPartitionSeries_deriv_eq_neg_mul_logDerivative_re hβ]
  field_simp [ne_of_gt (realPartitionSeries_pos β hβ)]

theorem partitionSeries_deriv_eq_neg_partitionSeries_mul_vonMangoldt
    {s : ℂ} (hs : 1 < s.re) :
    deriv partitionSeries s =
      -(partitionSeries s * LSeries (↗ArithmeticFunction.vonMangoldt) s) := by
  have hpart : partitionSeries s ≠ 0 := partitionSeries_ne_zero hs
  have hlog := partitionSeries_logDerivative_eq_vonMangoldt_LSeries hs
  have hmul :
      -deriv partitionSeries s =
        LSeries (↗ArithmeticFunction.vonMangoldt) s * partitionSeries s :=
    (div_eq_iff hpart).mp hlog
  calc
    deriv partitionSeries s = -(-deriv partitionSeries s) := by ring
    _ = -(LSeries (↗ArithmeticFunction.vonMangoldt) s * partitionSeries s) := by
      rw [hmul]
    _ = -(partitionSeries s * LSeries (↗ArithmeticFunction.vonMangoldt) s) := by
      rw [mul_comm]

theorem partitionSeries_logDerivative_eq_actualRiemannZetaLogDerivative
    {s : ℂ} (hs : 1 < s.re) :
    -deriv partitionSeries s / partitionSeries s =
      actualRiemannZetaLogDerivative s := by
  rw [partitionSeries_logDerivative_eq_vonMangoldt_LSeries hs,
    actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hs]

theorem partitionSeries_deriv_eq_neg_partitionSeries_mul_actualRiemannZetaLogDerivative
    {s : ℂ} (hs : 1 < s.re) :
    deriv partitionSeries s =
      -(partitionSeries s * actualRiemannZetaLogDerivative s) := by
  have hpart : partitionSeries s ≠ 0 := partitionSeries_ne_zero hs
  have hlog := partitionSeries_logDerivative_eq_actualRiemannZetaLogDerivative hs
  have hmul :
      -deriv partitionSeries s =
        actualRiemannZetaLogDerivative s * partitionSeries s :=
    (div_eq_iff hpart).mp hlog
  calc
    deriv partitionSeries s = -(-deriv partitionSeries s) := by ring
    _ = -(actualRiemannZetaLogDerivative s * partitionSeries s) := by
      rw [hmul]
    _ = -(partitionSeries s * actualRiemannZetaLogDerivative s) := by
      rw [mul_comm]

theorem realPartitionSeries_deriv_eq_neg_partitionSeries_mul_vonMangoldt_re
    {β : ℝ} (hβ : 1 < β) :
    deriv realPartitionSeries β =
      Complex.re (-(partitionSeries (β : ℂ) *
        (LSeries (↗ArithmeticFunction.vonMangoldt) (β : ℂ)))) := by
  have hs : 1 < (β : ℂ).re := by simpa using hβ
  have hcomplex :
      deriv partitionSeries (β : ℂ) =
        -(partitionSeries (β : ℂ) *
          LSeries (↗ArithmeticFunction.vonMangoldt) (β : ℂ)) := by
    exact partitionSeries_deriv_eq_neg_partitionSeries_mul_vonMangoldt hs
  have hreal :
      deriv realPartitionSeries β =
        (deriv partitionSeries (β : ℂ)).re := by
    rw [realPartitionSeries_deriv_eq_riemannZeta_deriv_re hβ]
    exact congrArg Complex.re
      (partitionSeries_deriv_eq_riemannZeta_deriv hs).symm
  rw [hreal, hcomplex]

theorem realPartitionSeries_log_deriv_eq_logDerivative
    {β : ℝ} (hβ : 1 < β) :
    deriv (fun x : ℝ => Real.log (realPartitionSeries x)) β =
      deriv realPartitionSeries β / realPartitionSeries β := by
  rw [deriv.log (realPartitionSeries_differentiableAt_of_one_lt hβ)
    (ne_of_gt (realPartitionSeries_pos β hβ))]

theorem realPartitionSeries_log_secondDeriv_eq_vonMangoldt_logMul_re
    {β : ℝ} (hβ : 1 < β) :
    deriv (fun x : ℝ =>
      deriv (fun y : ℝ => Real.log (realPartitionSeries y)) x) β =
      (LSeries
        (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
        (β : ℂ)).re := by
  have hU : ∀ᶠ z : ℂ in 𝓝 (β : ℂ), 1 < z.re := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds (show 1 < (β : ℂ).re by simpa using hβ)
  have heq :
      (fun z : ℂ => actualRiemannZetaLogDerivative z) =ᶠ[
        𝓝 (β : ℂ)]
        (fun z : ℂ => LSeries (↗ArithmeticFunction.vonMangoldt) z) := by
    filter_upwards [hU] with z hz
    exact actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hz
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have hdiff :
      DifferentiableAt ℂ actualRiemannZetaLogDerivative (β : ℂ) := by
    apply heq.differentiableAt_iff.2
    exact (LSeries_hasDerivAt
      (f := (↗ArithmeticFunction.vonMangoldt : ℕ → ℂ))
      (s := (β : ℂ)) (by simpa using hlt)).differentiableAt
  have hright : HasDerivAt
      (fun x : ℝ =>
        -(actualRiemannZetaLogDerivative (x : ℂ)).re)
      (-(deriv actualRiemannZetaLogDerivative (β : ℂ)).re) β := by
    simpa using hdiff.hasDerivAt.real_of_complex.neg
  have hfun :
      (fun x : ℝ =>
        deriv (fun y : ℝ => Real.log (realPartitionSeries y)) x) =ᶠ[
          𝓝 β]
        (fun x : ℝ =>
          -(actualRiemannZetaLogDerivative (x : ℂ)).re) := by
    filter_upwards [eventually_gt_nhds hβ] with x hx
    exact realPartitionSeries_log_deriv_eq_neg_logDerivative_re hx
  calc
    deriv (fun x : ℝ =>
        deriv (fun y : ℝ => Real.log (realPartitionSeries y)) x) β =
        deriv (fun x : ℝ =>
          -(actualRiemannZetaLogDerivative (x : ℂ)).re) β :=
      hfun.deriv_eq
    _ = -(deriv actualRiemannZetaLogDerivative (β : ℂ)).re :=
      hright.deriv
    _ = (LSeries
        (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
        (β : ℂ)).re := by
      rw [actualRiemannZetaLogDerivative_deriv_eq_neg_logMul hβ]
      simp

theorem realPartitionSeries_log_secondDeriv_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ deriv (fun x : ℝ =>
      deriv (fun y : ℝ => Real.log (realPartitionSeries y)) x) β := by
  rw [realPartitionSeries_log_secondDeriv_eq_vonMangoldt_logMul_re hβ]
  exact vonMangoldt_LSeries_logMul_nonneg hβ

/-- The one-parameter Fisher information of the actual real zeta partition
readout.  This is a definition on the real half-line; it makes no claim about
the complex Hessian of `log ζ` or about a pole asymptotic. -/
noncomputable def actualZetaRealFisherInformation (β : ℝ) : ℝ :=
  deriv (fun x : ℝ =>
    deriv (fun y : ℝ => Real.log (realPartitionSeries y)) x) β

theorem actualZetaRealFisherInformation_eq_vonMangoldt_logMul_re
    {β : ℝ} (hβ : 1 < β) :
    actualZetaRealFisherInformation β =
      (LSeries
        (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
        (β : ℂ)).re := by
  exact realPartitionSeries_log_secondDeriv_eq_vonMangoldt_logMul_re hβ

theorem actualZetaRealFisherInformation_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ actualZetaRealFisherInformation β := by
  exact realPartitionSeries_log_secondDeriv_nonneg hβ

theorem actualZetaRealFisherInformation_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < actualZetaRealFisherInformation β := by
  have hcoeff : ∀ n : ℕ,
      0 ≤ (LSeries.logMul
        (↗ArithmeticFunction.vonMangoldt) : ℕ → ℂ) n := by
    intro n
    rw [Complex.le_def]
    change 0 ≤ (Complex.log (n : ℂ) *
        (ArithmeticFunction.vonMangoldt n : ℂ)).re ∧
      0 = (Complex.log (n : ℂ) *
        (ArithmeticFunction.vonMangoldt n : ℂ)).im
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
      (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [hlog]
    constructor
    · simp only [Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (Real.log_natCast_nonneg n)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    · simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        mul_zero, zero_mul, add_zero]
  have htwo : 0 <
      (LSeries.logMul
        (↗ArithmeticFunction.vonMangoldt) : ℕ → ℂ) 2 := by
    simp only [LSeries.logMul]
    change 0 < Complex.log (2 : ℂ) *
      (ArithmeticFunction.vonMangoldt 2 : ℂ)
    have hp : Nat.Prime 2 := Nat.prime_two
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hlog2 : Complex.log (2 : ℂ) = (Real.log (2 : ℝ) : ℂ) := by
      convert (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm using 1 <;>
        norm_num
    rw [hlog2]
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    exact_mod_cast (mul_pos hlog hlog)
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv
        (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) < β := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact habs.trans_lt (by exact_mod_cast hβ)
  have hsum : LSeriesSummable
      (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) := by
    exact LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hlt)
  have hpos : 0 < LSeries
      (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) := by
    rw [LSeries]
    refine Summable.tsum_pos hsum (fun n => LSeries.term_nonneg
      (hcoeff n) β) 2 ?_
    exact LSeries.term_pos (by norm_num) htwo β
  rw [actualZetaRealFisherInformation_eq_vonMangoldt_logMul_re hβ]
  simpa using (Complex.lt_def.mp hpos).1

theorem actualZetaRealFisherInformation_deriv_eq_neg_curvature
    {β : ℝ} (hβ : 1 < β) :
    deriv actualZetaRealFisherInformation β =
      -actualVonMangoldtCurvature β := by
  have hU : ∀ᶠ z : ℂ in 𝓝 (β : ℂ), 1 < z.re := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds (show 1 < (β : ℂ).re by simpa using hβ)
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (LSeries.logMul
        (↗ArithmeticFunction.vonMangoldt)) < β := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact habs.trans_lt (by exact_mod_cast hβ)
  have hdiff : HasDerivAt
      (LSeries (LSeries.logMul
        (↗ArithmeticFunction.vonMangoldt)))
      (-LSeries
        (LSeries.logMul (LSeries.logMul
          (↗ArithmeticFunction.vonMangoldt))) (β : ℂ)) (β : ℂ) := by
    exact LSeries_hasDerivAt
      (f := (LSeries.logMul
        (↗ArithmeticFunction.vonMangoldt) : ℕ → ℂ))
      (s := (β : ℂ)) (by simpa using hlt)
  have hright : HasDerivAt
      (fun x : ℝ =>
        (LSeries (LSeries.logMul
          (↗ArithmeticFunction.vonMangoldt)) (x : ℂ)).re)
      (-LSeries
        (LSeries.logMul (LSeries.logMul
          (↗ArithmeticFunction.vonMangoldt))) (β : ℂ)).re β := by
    simpa using hdiff.real_of_complex
  have heq :
      (fun x : ℝ => actualZetaRealFisherInformation x) =ᶠ[𝓝 β]
        (fun x : ℝ =>
          (LSeries (LSeries.logMul
            (↗ArithmeticFunction.vonMangoldt)) (x : ℂ)).re) := by
    filter_upwards [eventually_gt_nhds hβ] with x hx
    exact actualZetaRealFisherInformation_eq_vonMangoldt_logMul_re hx
  calc
    deriv actualZetaRealFisherInformation β =
        deriv (fun x : ℝ =>
          (LSeries (LSeries.logMul
            (↗ArithmeticFunction.vonMangoldt)) (x : ℂ)).re) β :=
      heq.deriv_eq
    _ = (-LSeries
        (LSeries.logMul (LSeries.logMul
          (↗ArithmeticFunction.vonMangoldt))) (β : ℂ)).re :=
      hright.deriv
    _ = -actualVonMangoldtCurvature β := by
      rw [actualVonMangoldtCurvature_eq_double_logMul hβ]
      simp

end InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
