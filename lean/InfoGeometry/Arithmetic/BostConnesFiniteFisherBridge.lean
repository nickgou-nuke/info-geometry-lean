import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
import InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
import InfoGeometry.Canonical.SouriauMassieuHessianBridge
import InfoGeometry.Analytic.LogSumExpVariancePositivity

/-!
# Finite zeta-spectrum Fisher readout

This file packages the finite truncation indexed by `1, ..., N + 1` as a
`TwoChargeSpectrum`.  Its first charge is the logarithmic arithmetic energy
and its second charge is zero.  The resulting statements are finite Gibbs
and covariance facts only; no limiting zeta or Fisher asymptotic is claimed.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.BostConnesFiniteFisherBridge

open InfoGeometry.Canonical.SouriauMassieuHessianBridge
open InfoGeometry.Analytic
open Filter
open scoped Topology
open InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

def finiteZetaSpectrum (N : ℕ) : TwoChargeSpectrum where
  dim := N + 1
  weights := fun _ => 1
  h_pos := by
    intro i
    norm_num
  charge1 := fun i => Real.log (((i.val + 1 : ℕ) : ℝ))
  charge2 := fun _ => 0

theorem finiteZetaSpectrum_dim_pos (N : ℕ) :
    0 < (finiteZetaSpectrum N).dim := by
  simp [finiteZetaSpectrum]

theorem finiteZetaPartition_eq_log_exp_sum (N : ℕ) (β : ℝ) :
    partitionZ (finiteZetaSpectrum N) (-β) 0 =
      ∑ i : Fin (N + 1),
        Real.exp (-β * Real.log (((i.val + 1 : ℕ) : ℝ))) := by
  simp [partitionZ, gibbsWeight, finiteZetaSpectrum]

theorem finiteZetaPartition_eq_rpow_sum (N : ℕ) (β : ℝ) :
    partitionZ (finiteZetaSpectrum N) (-β) 0 =
      ∑ i : Fin (N + 1),
        Real.rpow (((i.val + 1 : ℕ) : ℝ)) (-β) := by
  rw [finiteZetaPartition_eq_log_exp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  calc
    Real.rpow (((i.val + 1 : ℕ) : ℝ)) (-β) =
        Real.exp (Real.log (((i.val + 1 : ℕ) : ℝ)) * (-β)) := by
          exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp (-β * Real.log (((i.val + 1 : ℕ) : ℝ))) := by
      congr 1
      ring

theorem finiteZetaPartition_eq_complex_partial_re (N : ℕ) (β : ℝ) :
    partitionZ (finiteZetaSpectrum N) (-β) 0 =
      (∑ i : Fin (N + 1),
        1 / (((i.val + 1 : ℕ) : ℂ) ^ (β : ℂ))).re := by
  rw [finiteZetaPartition_eq_rpow_sum]
  have hterm (i : Fin (N + 1)) :
      1 / (((i.val + 1 : ℕ) : ℂ) ^ (β : ℂ)) =
        (Real.rpow (((i.val + 1 : ℕ) : ℝ)) (-β) : ℂ) := by
    have hcast :
        (((i.val + 1 : ℕ) : ℂ)) =
          (((i.val + 1 : ℕ) : ℝ) : ℂ) := by
      norm_num
    rw [hcast]
    rw [← Complex.ofReal_cpow (by positivity :
      0 ≤ ((i.val + 1 : ℕ) : ℝ)) β]
    norm_cast
    rw [one_div, ← Real.rpow_neg (by positivity :
      0 ≤ ((i.val + 1 : ℕ) : ℝ))]
    norm_num
  have hsum :
      (∑ i : Fin (N + 1),
        1 / (((i.val + 1 : ℕ) : ℂ) ^ (β : ℂ))) =
      ∑ i : Fin (N + 1),
        (Real.rpow (((i.val + 1 : ℕ) : ℝ)) (-β) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i
  rw [hsum]
  simp

theorem finiteZetaPartition_eq_complex_partial_range (N : ℕ) (β : ℝ) :
    partitionZ (finiteZetaSpectrum N) (-β) 0 =
      (Finset.sum (Finset.range (N + 1))
        (fun n => 1 / ((n + 1 : ℕ) : ℂ) ^ (β : ℂ))).re := by
  rw [finiteZetaPartition_eq_complex_partial_re]
  apply congrArg Complex.re
  simpa using (Finset.sum_range
    (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ (β : ℂ)) (n := N + 1)).symm

theorem finiteZetaPartition_tendsto_realPartitionSeries
    {β : ℝ} (hβ : 1 < β) :
    Tendsto
      (fun N : ℕ => partitionZ (finiteZetaSpectrum N) (-β) 0)
      atTop (𝓝 (realPartitionSeries β)) := by
  have hsum :=
    InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge.partitionSeries_partial_sums_tendsto
    (s := (β : ℂ)) (by simpa using hβ)
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hsum
  have hsucc : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hlim := hre.comp hsucc
  rw [show realPartitionSeries β = (partitionSeries (β : ℂ)).re by rfl]
  convert hlim using 1
  funext N
  exact finiteZetaPartition_eq_complex_partial_range N β

theorem finiteZetaPartition_tendsto_riemannZeta_re
    {β : ℝ} (hβ : 1 < β) :
    Tendsto
      (fun N : ℕ => partitionZ (finiteZetaSpectrum N) (-β) 0)
      atTop (𝓝 ((riemannZeta (β : ℂ)).re)) := by
  rw [← realPartitionSeries_eq_riemannZeta β hβ]
  exact finiteZetaPartition_tendsto_realPartitionSeries hβ

/-! ## Finite Massieu/Fisher calculus -/

def finiteZetaLogPartition (N : ℕ) : ℝ → ℝ :=
  logSumExp
    (fun _ : Fin (N + 1) => 1)
    (fun i => -Real.log (((i.val + 1 : ℕ) : ℝ)))

theorem finiteZetaLogPartition_eq_log_partitionZ (N : ℕ) (β : ℝ) :
    finiteZetaLogPartition N β =
      Real.log (partitionZ (finiteZetaSpectrum N) (-β) 0) := by
  unfold finiteZetaLogPartition logSumExp logSumExpPartition
    partitionZ gibbsWeight finiteZetaSpectrum
  apply congrArg Real.log
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem finiteZetaLogPartition_tendsto_log_realPartitionSeries
    {β : ℝ} (hβ : 1 < β) :
    Tendsto
      (fun N : ℕ => finiteZetaLogPartition N β)
      atTop (𝓝 (Real.log (realPartitionSeries β))) := by
  have hpart := finiteZetaPartition_tendsto_realPartitionSeries hβ
  have hlog :=
    (Real.continuousAt_log
      (realPartitionSeries_pos β hβ).ne').tendsto.comp hpart
  have hfun :
      (fun N : ℕ => finiteZetaLogPartition N β) =
        (fun N : ℕ => Real.log (partitionZ (finiteZetaSpectrum N) (-β) 0)) := by
    funext N
    exact finiteZetaLogPartition_eq_log_partitionZ N β
  rw [hfun]
  exact hlog

theorem finiteZetaLogPartition_tendsto_log_riemannZeta_re
    {β : ℝ} (hβ : 1 < β) :
    Tendsto
      (fun N : ℕ => finiteZetaLogPartition N β)
      atTop (𝓝 (Real.log ((riemannZeta (β : ℂ)).re))) := by
  rw [← realPartitionSeries_eq_riemannZeta β hβ]
  exact finiteZetaLogPartition_tendsto_log_realPartitionSeries hβ

theorem finiteZetaLogPartition_eq_log_partitionZ_fun (N : ℕ) :
    finiteZetaLogPartition N =
      (fun β => Real.log (partitionZ (finiteZetaSpectrum N) (-β) 0)) := by
  funext β
  exact finiteZetaLogPartition_eq_log_partitionZ N β

theorem finiteZetaLogPartition_secondDeriv_eq_negativeLogVariance
    (N : ℕ) (β : ℝ) :
    deriv (fun t => deriv (finiteZetaLogPartition N) t) β =
      logSumExpVariance
        (fun _ : Fin (N + 1) => 1)
        (fun i => -Real.log (((i.val + 1 : ℕ) : ℝ))) β := by
  letI : Nonempty (Fin (N + 1)) := ⟨⟨0, by omega⟩⟩
  let w : Fin (N + 1) → ℝ := fun _ => 1
  let a : Fin (N + 1) → ℝ := fun i =>
    -Real.log (((i.val + 1 : ℕ) : ℝ))
  have hw : ∀ i, 0 < w i := by
    intro i
    simp [w]
  change deriv (fun t => deriv (logSumExp w a) t) β =
    logSumExpVariance w a β
  exact logSumExp_secondDeriv_eq_variance w a hw β

theorem finiteZetaLogPartition_secondDeriv_nonneg (N : ℕ) (β : ℝ) :
    0 ≤ deriv (fun t => deriv (finiteZetaLogPartition N) t) β := by
  letI : Nonempty (Fin (N + 1)) := ⟨⟨0, by omega⟩⟩
  let w : Fin (N + 1) → ℝ := fun _ => 1
  let a : Fin (N + 1) → ℝ := fun i =>
    -Real.log (((i.val + 1 : ℕ) : ℝ))
  have hw : ∀ i, 0 < w i := by
    intro i
    simp [w]
  change 0 ≤ deriv (fun t => deriv (logSumExp w a) t) β
  rw [logSumExp_secondDeriv_eq_variance w a hw β]
  exact logSumExpVariance_nonneg w a hw β

theorem finiteZetaLogPartition_secondDeriv_pos
    (N : ℕ) (hN : 0 < N) (β : ℝ) :
    0 < deriv (fun t => deriv (finiteZetaLogPartition N) t) β := by
  letI : Nonempty (Fin (N + 1)) := ⟨⟨0, by omega⟩⟩
  let w : Fin (N + 1) → ℝ := fun _ => 1
  let a : Fin (N + 1) → ℝ := fun i =>
    -Real.log (((i.val + 1 : ℕ) : ℝ))
  have hw : ∀ i, 0 < w i := by
    intro i
    simp [w]
  change 0 < deriv (fun t => deriv (logSumExp w a) t) β
  rw [logSumExp_secondDeriv_eq_variance w a hw β]
  apply logSumExpVariance_pos_of_exists_ne w a hw β
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  simp [a]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  linarith

theorem finiteZetaLogPartition_secondDeriv_nonneg_as_partition
    (N : ℕ) (β : ℝ) :
    0 ≤ deriv (fun t =>
      deriv (fun u => Real.log (partitionZ (finiteZetaSpectrum N) (-u) 0)) t) β := by
  rw [← finiteZetaLogPartition_eq_log_partitionZ_fun N]
  exact finiteZetaLogPartition_secondDeriv_nonneg N β

theorem finiteZetaPartition_pos (N : ℕ) (β : ℝ) :
    0 < partitionZ (finiteZetaSpectrum N) (-β) 0 := by
  exact partitionZ_pos_of_dim_pos _ _ _ (finiteZetaSpectrum_dim_pos N)

theorem finiteZetaLogCharge_variance_eq_logSumExpVariance
    (N : ℕ) (β : ℝ) :
    gibbsVar (finiteZetaSpectrum N) (-β) 0
        (fun i : Fin (finiteZetaSpectrum N).dim =>
          Real.log (((i.val + 1 : ℕ) : ℝ))) =
      logSumExpVariance
        (fun _ : Fin (N + 1) => 1)
        (fun i => -Real.log (((i.val + 1 : ℕ) : ℝ))) β := by
  let a : Fin (N + 1) → ℝ := fun i =>
    -Real.log (((i.val + 1 : ℕ) : ℝ))
  have hpart :
      logSumExpPartition (fun _ : Fin (N + 1) => 1) a β =
        partitionZ (finiteZetaSpectrum N) (-β) 0 := by
    unfold logSumExpPartition partitionZ gibbsWeight a
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp [finiteZetaSpectrum]
  have hweight (i : Fin (N + 1)) :
      logSumExpWeight (fun _ : Fin (N + 1) => 1) a β i =
        gibbsWeight (finiteZetaSpectrum N) (-β) 0 i /
          partitionZ (finiteZetaSpectrum N) (-β) 0 := by
    unfold logSumExpWeight
    rw [hpart]
    simp [gibbsWeight, finiteZetaSpectrum, a]
  have hleft :
      gibbsVar (finiteZetaSpectrum N) (-β) 0
          (fun i : Fin (finiteZetaSpectrum N).dim =>
            Real.log (((i.val + 1 : ℕ) : ℝ))) =
        gibbsVar (finiteZetaSpectrum N) (-β) 0 a := by
    have ha_neg :
        (-a) = (fun i : Fin (N + 1) =>
          Real.log (((i.val + 1 : ℕ) : ℝ))) := by
      funext i
      simp [a, Pi.neg_apply]
    calc
      gibbsVar (finiteZetaSpectrum N) (-β) 0
          (fun i : Fin (finiteZetaSpectrum N).dim =>
            Real.log (((i.val + 1 : ℕ) : ℝ))) =
          gibbsVar (finiteZetaSpectrum N) (-β) 0 (-a) := by
            rw [ha_neg]
            rfl
      _ = gibbsVar (finiteZetaSpectrum N) (-β) 0 a :=
        gibbsVar_neg (finiteZetaSpectrum N) (-β) 0 a
  rw [hleft, logSumExpVariance_eq_centered
    (fun _ : Fin (N + 1) => 1) a (by intro i; norm_num) β]
  unfold gibbsVar gibbsCov gibbsMean
  simp_rw [hweight]
  have hZ :
      partitionZ (finiteZetaSpectrum N) (-β) 0 ≠ 0 :=
    (finiteZetaPartition_pos N β).ne'
  have hmean :
      (∑ i : Fin (N + 1),
          gibbsWeight (finiteZetaSpectrum N) (-β) 0 i * a i) /
          partitionZ (finiteZetaSpectrum N) (-β) 0 =
        ∑ i : Fin (N + 1),
          (gibbsWeight (finiteZetaSpectrum N) (-β) 0 i /
            partitionZ (finiteZetaSpectrum N) (-β) 0) * a i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
  have hsq :
      (∑ i : Fin (N + 1),
          gibbsWeight (finiteZetaSpectrum N) (-β) 0 i *
            (a i -
              (∑ j : Fin (N + 1),
                gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
                partitionZ (finiteZetaSpectrum N) (-β) 0) *
            (a i -
              (∑ j : Fin (N + 1),
                gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
                partitionZ (finiteZetaSpectrum N) (-β) 0)) =
        ∑ i : Fin (N + 1),
          gibbsWeight (finiteZetaSpectrum N) (-β) 0 i *
            (a i -
              (∑ j : Fin (N + 1),
                gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
                partitionZ (finiteZetaSpectrum N) (-β) 0) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have houter :
      (∑ i : Fin (N + 1),
          gibbsWeight (finiteZetaSpectrum N) (-β) 0 i *
            (a i -
              (∑ j : Fin (N + 1),
                gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
                partitionZ (finiteZetaSpectrum N) (-β) 0) ^ 2) /
          partitionZ (finiteZetaSpectrum N) (-β) 0 =
        ∑ i : Fin (N + 1),
          (gibbsWeight (finiteZetaSpectrum N) (-β) 0 i /
            partitionZ (finiteZetaSpectrum N) (-β) 0) *
            (a i -
              (∑ j : Fin (N + 1),
                gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
                partitionZ (finiteZetaSpectrum N) (-β) 0) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
  calc
    (∑ i : Fin (N + 1),
        gibbsWeight (finiteZetaSpectrum N) (-β) 0 i *
          (a i -
            (∑ j : Fin (N + 1),
              gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
              partitionZ (finiteZetaSpectrum N) (-β) 0) *
          (a i -
            (∑ j : Fin (N + 1),
              gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
              partitionZ (finiteZetaSpectrum N) (-β) 0)) /
        partitionZ (finiteZetaSpectrum N) (-β) 0 =
      (∑ i : Fin (N + 1),
        gibbsWeight (finiteZetaSpectrum N) (-β) 0 i *
          (a i -
            (∑ j : Fin (N + 1),
              gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
              partitionZ (finiteZetaSpectrum N) (-β) 0) ^ 2) /
        partitionZ (finiteZetaSpectrum N) (-β) 0 := by
          congr 1
    _ = ∑ i : Fin (N + 1),
        (gibbsWeight (finiteZetaSpectrum N) (-β) 0 i /
          partitionZ (finiteZetaSpectrum N) (-β) 0) *
          (a i -
            (∑ j : Fin (N + 1),
              gibbsWeight (finiteZetaSpectrum N) (-β) 0 j * a j) /
              partitionZ (finiteZetaSpectrum N) (-β) 0) ^ 2 := houter
    _ = ∑ i : Fin (N + 1),
        (gibbsWeight (finiteZetaSpectrum N) (-β) 0 i /
          partitionZ (finiteZetaSpectrum N) (-β) 0) *
          (a i - ∑ j : Fin (N + 1),
            gibbsWeight (finiteZetaSpectrum N) (-β) 0 j /
              partitionZ (finiteZetaSpectrum N) (-β) 0 * a j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hmean]

theorem finiteZetaLogPartition_secondDeriv_eq_logCharge_variance
    (N : ℕ) (β : ℝ) :
    deriv (fun t => deriv (finiteZetaLogPartition N) t) β =
      gibbsVar (finiteZetaSpectrum N) (-β) 0
        (fun i : Fin (finiteZetaSpectrum N).dim =>
          Real.log (((i.val + 1 : ℕ) : ℝ))) := by
  rw [finiteZetaLogPartition_secondDeriv_eq_negativeLogVariance]
  exact (finiteZetaLogCharge_variance_eq_logSumExpVariance N β).symm

theorem finiteZetaLogCharge_variance_nonneg (N : ℕ) (β : ℝ) :
    0 ≤ gibbsVar (finiteZetaSpectrum N) (-β) 0
      (fun i : Fin (finiteZetaSpectrum N).dim =>
        Real.log (((i.val + 1 : ℕ) : ℝ))) := by
  exact gibbsVar_nonneg_of_dim_pos _ _ _ _ (finiteZetaSpectrum_dim_pos N)

theorem finiteZetaLogCharge_variance_pos
    (N : ℕ) (hN : 0 < N) (β : ℝ) :
    0 < gibbsVar (finiteZetaSpectrum N) (-β) 0
      (fun i : Fin (finiteZetaSpectrum N).dim =>
        Real.log (((i.val + 1 : ℕ) : ℝ))) := by
  rw [← finiteZetaLogPartition_secondDeriv_eq_logCharge_variance N β]
  exact finiteZetaLogPartition_secondDeriv_pos N hN β

theorem finiteZetaCovariance_determinant_nonneg (N : ℕ) (β : ℝ) :
    0 ≤
      gibbsVar (finiteZetaSpectrum N) (-β) 0
          (finiteZetaSpectrum N).charge1 *
        gibbsVar (finiteZetaSpectrum N) (-β) 0
          (finiteZetaSpectrum N).charge2 -
        (gibbsCov (finiteZetaSpectrum N) (-β) 0
          (finiteZetaSpectrum N).charge1 (finiteZetaSpectrum N).charge2) ^ 2 := by
  exact charge_covariance_det_nonneg_of_dim_pos _ _ _
    (finiteZetaSpectrum_dim_pos N)

/-! The zero second charge has zero variance and is orthogonal to every
finite observable for the Gibbs covariance. -/

theorem finiteZeta_secondCharge_variance_zero (N : ℕ) (β : ℝ) :
    gibbsVar (finiteZetaSpectrum N) (-β) 0
      (finiteZetaSpectrum N).charge2 = 0 := by
  simp [finiteZetaSpectrum, gibbsVar, gibbsCov, gibbsMean]

theorem finiteZeta_logCharge_secondCharge_covariance_zero
    (N : ℕ) (β : ℝ) :
    gibbsCov (finiteZetaSpectrum N) (-β) 0
      (finiteZetaSpectrum N).charge1 (finiteZetaSpectrum N).charge2 = 0 := by
  simp [finiteZetaSpectrum, gibbsCov, gibbsMean]

/-! The second charge is identically zero in this finite zeta truncation.  Thus
the two-charge covariance matrix is not merely positive semidefinite: it has
rank at most one, with vanishing determinant. -/

theorem finiteZetaCovariance_determinant_eq_zero (N : ℕ) (β : ℝ) :
    gibbsVar (finiteZetaSpectrum N) (-β) 0
          (finiteZetaSpectrum N).charge1 *
        gibbsVar (finiteZetaSpectrum N) (-β) 0
          (finiteZetaSpectrum N).charge2 -
        (gibbsCov (finiteZetaSpectrum N) (-β) 0
          (finiteZetaSpectrum N).charge1 (finiteZetaSpectrum N).charge2) ^ 2 = 0 := by
  rw [finiteZeta_secondCharge_variance_zero N β,
    finiteZeta_logCharge_secondCharge_covariance_zero N β]
  ring

end InfoGeometry.Arithmetic.BostConnesFiniteFisherBridge
