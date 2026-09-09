import InfoGeometry.Probability.FiniteLogTransport
import InfoGeometry.Probability.DetectorScaleInvariance
import InfoGeometry.Projective.WeylLogScaleBridge

/-! Extensions of the canonical finite transport owner: geometric-mean
preservation, Weyl surprisal action and uniqueness of exact factorization.
CAS companion: scripts/verify_detector_ensemble.py. -/
noncomputable section
open scoped BigOperators
namespace InfoGeometry.Probability.DetectorEnsembleTransport
open InfoGeometry.Probability.DetectorScaleInvariance
open InfoGeometry.Probability.FiniteLogTransport
open InfoGeometry.Projective.WeylLogScaleBridge

theorem transport_preserves_row_product {m : ℕ} (hm : 0 < m)
    (L s : Fin m → ℝ) :
    (∏ j, transport L s j) = ∏ j, L j := by
  simp only [transport, Finset.prod_mul_distrib]
  rw [← Real.exp_sum, Finset.sum_neg_distrib, sum_center hm s]
  simp

theorem rateSurprisal_weyl (L U σ : ℝ) (hL : 0 < L) (hU : 0 < U) :
    rateSurprisal (weylFieldAction 1 σ L) U = rateSurprisal L U - σ := by
  unfold rateSurprisal weylFieldAction
  rw [one_mul, Real.log_div (mul_pos (Real.exp_pos σ) hL).ne' hU.ne',
    Real.log_mul (Real.exp_ne_zero σ) hL.ne', Real.log_exp,
    Real.log_div hL.ne' hU.ne']
  ring

theorem gauge_center_residual {m : ℕ} (ell μ : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    ell - (μ + mean s) - center s j = ell - μ - s j := by
  unfold center
  ring

theorem centered_factorization_unique {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (μ ν : Fin n → ℝ) (s t : Fin m → ℝ)
    (hs : ∑ j, s j = 0) (ht : ∑ j, t j = 0)
    (h : ∀ i j, μ i + s j = ν i + t j) : μ = ν ∧ s = t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hμ : μ = ν := by
    funext i
    have hh := congrArg (fun f : Fin m → ℝ => ∑ j, f j) (funext (h i))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hs, ht, add_zero] at hh
    exact mul_left_cancel₀ hmR hh
  refine ⟨hμ, ?_⟩
  funext j
  have hh := h ⟨0, hn⟩ j
  rw [hμ] at hh
  exact add_left_cancel hh

example : center (![0, 2, 4] : Fin 3 → ℝ) = ![-2, 0, 2] := by
  ext j
  fin_cases j <;> norm_num [center, mean, Fin.sum_univ_succ]

end InfoGeometry.Probability.DetectorEnsembleTransport
