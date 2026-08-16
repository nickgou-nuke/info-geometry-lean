import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge

/-!
# Native Dirichlet-series readout for the Bost--Connes partition

This owner records only the convergent arithmetic series and its Mathlib zeta
identification.  It does not define a KMS state or a C*-dynamical system.
-/

namespace InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

open scoped LSeries.notation
open scoped ComplexOrder
open scoped Topology
open Filter
open ArithmeticFunction
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge

noncomputable def partitionSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s

theorem partitionSeries_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    partitionSeries s = riemannZeta s := by
  unfold partitionSeries
  simpa [Nat.cast_add] using (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm

theorem partitionSeries_ne_zero {s : ℂ} (hs : 1 < s.re) :
    partitionSeries s ≠ 0 := by
  rw [partitionSeries_eq_riemannZeta hs]
  exact riemannZeta_ne_zero_of_one_lt_re hs

theorem actualRiemannZeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (𝓝 1) := by
  exact riemannZeta_residue_one

theorem actualRiemannZeta_sub_one_div_tendsto_nhds_right :
    Tendsto (fun β : ℝ => riemannZeta β - 1 / (β - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  convert ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right using 1

/-! ## Real inverse-temperature readout -/

/-- The real part of the native partition series at a real inverse temperature. -/
noncomputable def realPartitionSeries (β : ℝ) : ℝ :=
  (partitionSeries (β : ℂ)).re

theorem realPartitionSeries_eq_riemannZeta (β : ℝ) (hβ : 1 < β) :
    realPartitionSeries β = (riemannZeta (β : ℂ)).re := by
  rw [realPartitionSeries,
    partitionSeries_eq_riemannZeta (by simpa using hβ)]

theorem realPartitionSeries_pos (β : ℝ) (hβ : 1 < β) :
    0 < realPartitionSeries β := by
  rw [realPartitionSeries_eq_riemannZeta β hβ]
  exact riemannZeta_re_pos_of_one_lt hβ

theorem realPartitionSeries_ne_zero (β : ℝ) (hβ : 1 < β) :
    realPartitionSeries β ≠ 0 :=
  ne_of_gt (realPartitionSeries_pos β hβ)

theorem vonMangoldt_LSeries_abscissaOfAbsConv_le_one :
    LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < (y : ℂ).re by simp only [Complex.ofReal_re, hy])

theorem vonMangoldt_LSeries_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ (L ↗ArithmeticFunction.vonMangoldt (β : ℂ)).re := by
  have hcoeff : ∀ n : ℕ,
      0 ≤ (↗ArithmeticFunction.vonMangoldt : ℕ → ℂ) n := by
    intro n
    rw [Complex.le_def]
    constructor
    · simpa using ArithmeticFunction.vonMangoldt_nonneg (n := n)
    · simp
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have h := LSeries.iteratedDeriv_alternating hcoeff hlt 0
  have hre := (Complex.le_def.mp h).1
  simpa using hre

theorem vonMangoldt_LSeries_first_deriv_nonpos
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ -(iteratedDeriv 1 (LSeries (↗ArithmeticFunction.vonMangoldt)) β).re := by
  have hcoeff : ∀ n : ℕ,
      0 ≤ (↗ArithmeticFunction.vonMangoldt : ℕ → ℂ) n := by
    intro n
    rw [Complex.le_def]
    constructor
    · simpa using ArithmeticFunction.vonMangoldt_nonneg (n := n)
    · simp
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have h := LSeries.iteratedDeriv_alternating hcoeff hlt 1
  have hre := (Complex.le_def.mp h).1
  simpa [pow_one] using hre

theorem vonMangoldt_LSeries_logMul_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ (LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
      (β : ℂ)).re := by
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have h := vonMangoldt_LSeries_first_deriv_nonpos hβ
  rw [iteratedDeriv_one, LSeries_deriv hlt] at h
  simpa using h

theorem actualRiemannZetaLogDerivative_deriv_eq_neg_logMul
    {β : ℝ} (hβ : 1 < β) :
    deriv actualRiemannZetaLogDerivative (β : ℂ) =
      -LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) := by
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have hU : ∀ᶠ z : ℂ in nhds (β : ℂ), 1 < z.re := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds (show 1 < (β : ℂ).re by simpa using hβ)
  have heq :
      (fun z : ℂ =>
        actualRiemannZetaLogDerivative z) =ᶠ[nhds (β : ℂ)]
      (fun z : ℂ => LSeries (↗ArithmeticFunction.vonMangoldt) z) := by
    filter_upwards [hU] with z hz
    exact actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hz
  calc
    deriv
        actualRiemannZetaLogDerivative (β : ℂ) =
        deriv (LSeries (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) := by
          exact heq.deriv_eq
    _ = -LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) := by
      exact LSeries_deriv hlt

theorem actualRiemannZetaLogDerivative_deriv_real_nonpos
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ -(deriv actualRiemannZetaLogDerivative (β : ℂ)).re := by
  rw [actualRiemannZetaLogDerivative_deriv_eq_neg_logMul hβ]
  simpa using vonMangoldt_LSeries_logMul_nonneg hβ

theorem vonMangoldt_LSeries_second_iteratedDeriv_eq_logMul
    {β : ℝ} (hβ : 1 < β) :
    iteratedDeriv 2 (LSeries (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) =
      LSeries
        (LSeries.logMul
          (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))) (β : ℂ) := by
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have hlt_logMul :
      LSeries.abscissaOfAbsConv
        (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) < β := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact hlt
  have hU : ∀ᶠ z : ℂ in nhds (β : ℂ), 1 < z.re := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds (show 1 < (β : ℂ).re by simpa using hβ)
  have hderiv :
      (fun z : ℂ => deriv (LSeries (↗ArithmeticFunction.vonMangoldt)) z) =ᶠ[
        nhds (β : ℂ)]
      (fun z : ℂ =>
        -LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) z) := by
    filter_upwards [hU] with z hz
    have hz' : (1 : EReal) < (z.re : EReal) := by
      exact_mod_cast hz
    exact LSeries_deriv (habs.trans_lt hz')
  calc
    iteratedDeriv 2 (LSeries (↗ArithmeticFunction.vonMangoldt)) (β : ℂ) =
        deriv (iteratedDeriv 1 (LSeries (↗ArithmeticFunction.vonMangoldt)))
          (β : ℂ) := by rw [iteratedDeriv_succ]
    _ = deriv (deriv (LSeries (↗ArithmeticFunction.vonMangoldt))) (β : ℂ) := by
      rw [iteratedDeriv_one]
    _ = deriv
        (fun z : ℂ =>
          -LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)) z)
        (β : ℂ) := by
      exact hderiv.deriv_eq
    _ = -deriv (LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)))
        (β : ℂ) := by
      have hderivβ := LSeries_hasDerivAt
        (f := LSeries.logMul (↗ArithmeticFunction.vonMangoldt : ℕ → ℂ))
        (s := (β : ℂ)) (by simpa using hlt_logMul)
      have hneg := hderivβ.neg.deriv
      rw [LSeries_deriv hlt_logMul]
      simpa only [Pi.neg_apply] using hneg
    _ = LSeries
        (LSeries.logMul (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)))
        (β : ℂ) := by
      rw [LSeries_deriv hlt_logMul]
      simp

theorem vonMangoldt_LSeries_second_iteratedDeriv_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ (iteratedDeriv 2 (LSeries (↗ArithmeticFunction.vonMangoldt)) β).re := by
  have hcoeff : ∀ n : ℕ,
      0 ≤ (↗ArithmeticFunction.vonMangoldt : ℕ → ℂ) n := by
    intro n
    rw [Complex.le_def]
    constructor
    · simpa using ArithmeticFunction.vonMangoldt_nonneg (n := n)
    · simp
  have habs :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) ≤ 1 :=
    vonMangoldt_LSeries_abscissaOfAbsConv_le_one
  have hlt :
      LSeries.abscissaOfAbsConv (↗ArithmeticFunction.vonMangoldt) < β :=
    habs.trans_lt (by exact_mod_cast hβ)
  have h := LSeries.iteratedDeriv_alternating hcoeff hlt 2
  have hre := (Complex.le_def.mp h).1
  simpa [pow_two] using hre

theorem vonMangoldt_LSeries_double_logMul_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤
      (LSeries
        (LSeries.logMul
          (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))) (β : ℂ)).re := by
  rw [← vonMangoldt_LSeries_second_iteratedDeriv_eq_logMul hβ]
  exact vonMangoldt_LSeries_second_iteratedDeriv_nonneg hβ

theorem actualRiemannZetaLogDerivative_second_iteratedDeriv_eq_double_logMul
    {β : ℝ} (hβ : 1 < β) :
    iteratedDeriv 2 actualRiemannZetaLogDerivative (β : ℂ) =
      LSeries
        (LSeries.logMul
          (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))) (β : ℂ) := by
  have hU : ∀ᶠ z : ℂ in nhds (β : ℂ), 1 < z.re := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds (show 1 < (β : ℂ).re by simpa using hβ)
  have hderiv :
      (fun z : ℂ => deriv actualRiemannZetaLogDerivative z) =ᶠ[
        nhds (β : ℂ)]
      (fun z : ℂ => deriv (LSeries (↗ArithmeticFunction.vonMangoldt)) z) := by
    filter_upwards [hU] with z hz
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hlocal : ∀ᶠ w : ℂ in nhds z, 1 < w.re :=
      hopen.mem_nhds hz
    have heq :
        (fun w : ℂ => actualRiemannZetaLogDerivative w) =ᶠ[nhds z]
          (fun w : ℂ => LSeries (↗ArithmeticFunction.vonMangoldt) w) := by
      filter_upwards [hlocal] with w hw
      exact actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hw
    exact heq.deriv_eq
  calc
    iteratedDeriv 2 actualRiemannZetaLogDerivative (β : ℂ) =
        deriv (deriv actualRiemannZetaLogDerivative) (β : ℂ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    _ = deriv (deriv (LSeries (↗ArithmeticFunction.vonMangoldt)))
        (β : ℂ) := hderiv.deriv_eq
    _ = iteratedDeriv 2 (LSeries (↗ArithmeticFunction.vonMangoldt))
        (β : ℂ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    _ = LSeries
        (LSeries.logMul
          (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))) (β : ℂ) :=
      vonMangoldt_LSeries_second_iteratedDeriv_eq_logMul hβ

theorem actualRiemannZetaLogDerivative_second_iteratedDeriv_real_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ (iteratedDeriv 2 actualRiemannZetaLogDerivative (β : ℂ)).re := by
  rw [actualRiemannZetaLogDerivative_second_iteratedDeriv_eq_double_logMul hβ]
  exact vonMangoldt_LSeries_double_logMul_nonneg hβ

/-! ## Named actual curvature readout -/

/-- The real von-Mangoldt curvature readout on the absolute-convergence half-plane.
This is not identified here with the Gibbs Fisher metric. -/
noncomputable def actualVonMangoldtCurvature (β : ℝ) : ℝ :=
  (iteratedDeriv 2 actualRiemannZetaLogDerivative (β : ℂ)).re

theorem actualVonMangoldtCurvature_eq_double_logMul
    {β : ℝ} (hβ : 1 < β) :
    actualVonMangoldtCurvature β =
      (LSeries
        (LSeries.logMul
          (LSeries.logMul (↗ArithmeticFunction.vonMangoldt)))
        (β : ℂ)).re := by
  simpa [actualVonMangoldtCurvature] using congrArg Complex.re
    (actualRiemannZetaLogDerivative_second_iteratedDeriv_eq_double_logMul hβ)

theorem actualVonMangoldtCurvature_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ actualVonMangoldtCurvature β := by
  exact actualRiemannZetaLogDerivative_second_iteratedDeriv_real_nonneg hβ

theorem partitionSeries_deriv_eq_riemannZeta_deriv
    {s : ℂ} (hs : 1 < s.re) :
    deriv partitionSeries s = deriv riemannZeta s := by
  apply Filter.EventuallyEq.deriv_eq
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact partitionSeries_eq_riemannZeta hz

theorem partitionSeries_logDerivative_eq_vonMangoldt_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    -deriv partitionSeries s / partitionSeries s = L ↗Λ s := by
  have hpart : partitionSeries s ≠ 0 := partitionSeries_ne_zero hs
  apply (div_eq_iff hpart).2
  calc
    -deriv partitionSeries s = -deriv riemannZeta s := by
      rw [partitionSeries_deriv_eq_riemannZeta_deriv hs]
    _ = riemannZeta s * (L ↗Λ s) := by
      rw [vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs]
      dsimp [actualRiemannZetaLogDerivative]
      field_simp [riemannZeta_ne_zero_of_one_lt_re hs]
    _ = (L ↗Λ s) * partitionSeries s := by
      rw [partitionSeries_eq_riemannZeta hs, mul_comm]

theorem partitionSeries_logDerivative_real_nonpos
    {β : ℝ} (hβ : 1 < β) :
    0 ≤
      (-deriv partitionSeries (β : ℂ) /
        partitionSeries (β : ℂ)).re := by
  rw [partitionSeries_logDerivative_eq_vonMangoldt_LSeries (by simpa using hβ)]
  exact vonMangoldt_LSeries_nonneg hβ

theorem summable_partitionSeries_summand (s : ℂ) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) ↔ 1 < s.re := by
  simpa [Nat.cast_add] using
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).trans
      (Complex.summable_one_div_nat_cpow (p := s))

theorem not_summable_harmonic_shift :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
  simpa [Nat.cast_add] using h

end InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
