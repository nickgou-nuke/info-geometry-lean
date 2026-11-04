/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NilpotentPairingAnomalyToChiralBlockGapPoset
import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.QuantumGeometry.TensorBridge

/-!
# Chiral nilpotent anomaly and Robertson uncertainty

This bridge places the anomaly-first chiral block identities on a complex
Hilbert space. It identifies the Berry curvature of the two skew-adjoint
generators `i Φ` and `J` with the state expectation of the parity anomaly
`Σ`, then applies the existing QGT Robertson bound. The positivity and state
interpretation live on the Hilbert carrier; they are not inferred from the
bare ring identities.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.ChiralAnomalyRobertsonBridge

open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.QuantumGeometry.TensorBridge
open OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset
open ContinuousLinearMap
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- The parity anomaly `[N, N*]` is self-adjoint on the Hilbert operator space. -/
theorem Sigma_selfAdjoint (N : EndH) : star (Sigma N) = Sigma N := by
  change star (N * star N - star N * N) = N * star N - star N * N
  simp only [star_sub, star_mul, star_star]

/-- The expectation of the anomaly-square operator is the squared Hilbert norm
of the anomalous state vector. In particular, it is nonnegative. -/
theorem gap_expectation_eq_anomaly_norm_sq (N : EndH) (ψ : H) :
    (inner ℂ ψ (Gap N ψ)).re = ‖Sigma N ψ‖ ^ 2 := by
  have h_adj : ContinuousLinearMap.adjoint (Sigma N) = Sigma N := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact Sigma_selfAdjoint N
  have h_inner := adjoint_inner_right (Sigma N) ψ (Sigma N ψ)
  rw [h_adj] at h_inner
  change (inner ℂ ψ (Sigma N (Sigma N ψ))).re = ‖Sigma N ψ‖ ^ 2
  rw [h_inner, inner_self_eq_norm_sq_to_K]
  change (Complex.ofReal (‖Sigma N ψ‖) ^ 2).re = ‖Sigma N ψ‖ ^ 2
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re _

/-- The square-gap and anomaly have the same zero modes on the Hilbert space:
`Gap N ψ = 0` exactly when `Σ N ψ = 0`. -/
theorem gap_kernel_iff_anomaly_kernel (N : EndH) (ψ : H) :
    Gap N ψ = 0 ↔ Sigma N ψ = 0 := by
  constructor
  · intro h_gap
    have h_expect : (inner ℂ ψ (Gap N ψ)).re = 0 := by
      rw [h_gap]
      simp
    have h_norm_sq : ‖Sigma N ψ‖ ^ 2 = 0 := by
      rw [← gap_expectation_eq_anomaly_norm_sq]
      exact h_expect
    have h_norm : ‖Sigma N ψ‖ = 0 := by
      nlinarith [sq_nonneg (‖Sigma N ψ‖ : ℝ)]
    exact norm_eq_zero.mp h_norm
  · intro h_sigma
    change Sigma N (Sigma N ψ) = 0
    simpa using congrArg (fun v : H => Sigma N v) h_sigma

/-- Positivity of the anomaly-square gap on every Hilbert-space vector. -/
theorem gap_expectation_nonneg (N : EndH) (ψ : H) :
    0 ≤ (inner ℂ ψ (Gap N ψ)).re := by
  rw [gap_expectation_eq_anomaly_norm_sq]
  exact sq_nonneg _

/-- The anomaly-square operator is self-adjoint. -/
theorem Gap_selfAdjoint (N : EndH) : star (Gap N) = Gap N := by
  change star (Sigma N * Sigma N) = Sigma N * Sigma N
  rw [star_mul, Sigma_selfAdjoint]

/-- When the chiral anomaly is a regular nilpotent pair, `Gap` is idempotent
and its state expectation is the squared norm of the projected state. -/
theorem regular_gap_expectation_eq_norm_sq (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    (inner ℂ ψ (Gap N ψ)).re = ‖Gap N ψ‖ ^ 2 := by
  have h_adj : ContinuousLinearMap.adjoint (Gap N) = Gap N := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact Gap_selfAdjoint N
  have h_inner := adjoint_inner_right (Gap N) ψ (Gap N ψ)
  rw [h_adj] at h_inner
  have h_gap_apply : Gap N (Gap N ψ) = Gap N ψ := by
    have h := congrArg (fun T : EndH => T ψ) (Gap_idem N h_nil h_reg)
    simpa using h
  calc (inner ℂ ψ (Gap N ψ)).re
      = (inner ℂ ψ (Gap N (Gap N ψ))).re := by rw [h_gap_apply]
    _ = (inner ℂ (Gap N ψ) (Gap N ψ)).re := congrArg Complex.re h_inner
    _ = ‖Gap N ψ‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      change (Complex.ofReal (‖Gap N ψ‖) ^ 2).re = ‖Gap N ψ‖ ^ 2
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_re _

/-- On the regular support, the projected state and its anomaly image have
the same Hilbert norm. -/
theorem regular_gap_norm_eq_anomaly_norm (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    ‖Gap N ψ‖ = ‖Sigma N ψ‖ := by
  have h_sq : ‖Gap N ψ‖ ^ 2 = ‖Sigma N ψ‖ ^ 2 := by
    calc ‖Gap N ψ‖ ^ 2 = (inner ℂ ψ (Gap N ψ)).re :=
          (regular_gap_expectation_eq_norm_sq N h_nil h_reg ψ).symm
      _ = ‖Sigma N ψ‖ ^ 2 := gap_expectation_eq_anomaly_norm_sq N ψ
  nlinarith [norm_nonneg (Gap N ψ), norm_nonneg (Sigma N ψ)]

/-- For a regular nilpotent pair, the range of the support projection is
exactly the range of the parity anomaly. -/
theorem regular_gap_range_eq_anomaly_range (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Set.range (fun ψ : H => Gap N ψ) = Set.range (fun ψ : H => Sigma N ψ) := by
  ext y
  constructor
  · rintro ⟨ψ, rfl⟩
    refine ⟨Sigma N ψ, ?_⟩
    simp [Gap]
  · rintro ⟨ψ, rfl⟩
    refine ⟨Sigma N ψ, ?_⟩
    have h := congrArg (fun T : EndH => T ψ) (Gap_mul_Sigma N h_nil h_reg)
    simpa using h

/-- Restricted to the regular anomaly support, the parity anomaly is an
involution: applying it twice fixes every supported vector. -/
theorem regular_anomaly_involution_on_gap_support (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    Sigma N (Sigma N (Gap N ψ)) = Gap N ψ := by
  have h := congrArg (fun T : EndH => T ψ) (Gap_idem N h_nil h_reg)
  simpa [Gap] using h

/-- The regular anomaly support and its complementary projection give an
orthogonal Pythagorean decomposition of every Hilbert-space vector. -/
theorem regular_gap_pythagorean_decomposition (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    ‖ψ‖ ^ 2 = ‖Gap N ψ‖ ^ 2 + ‖(1 - Gap N) ψ‖ ^ 2 := by
  have h_adj : ContinuousLinearMap.adjoint (Gap N) = Gap N := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact Gap_selfAdjoint N
  have h_idem : Gap N * Gap N = Gap N := Gap_idem N h_nil h_reg
  have h_gap_comp : Gap N * (1 - Gap N) = 0 := by
    rw [mul_sub, mul_one, h_idem, sub_self]
  have h_orth : inner ℂ (Gap N ψ) ((1 - Gap N) ψ) = 0 := by
    have h_inner := adjoint_inner_right (Gap N) ψ ((1 - Gap N) ψ)
    rw [h_adj] at h_inner
    have h_annihilate : Gap N ((1 - Gap N) ψ) = 0 := by
      have h := congrArg (fun T : EndH => T ψ) h_gap_comp
      simpa using h
    rw [h_annihilate] at h_inner
    simpa using h_inner.symm
  have h_split : ψ = Gap N ψ + (1 - Gap N) ψ := by
    change ψ = Gap N ψ + (ψ - Gap N ψ)
    calc ψ = (ψ - Gap N ψ) + Gap N ψ := (sub_add_cancel ψ (Gap N ψ)).symm
      _ = Gap N ψ + (ψ - Gap N ψ) := add_comm _ _
  have h_pyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (Gap N ψ) ((1 - Gap N) ψ) h_orth
  calc ‖ψ‖ ^ 2 = ‖Gap N ψ + (1 - Gap N) ψ‖ ^ 2 :=
      congrArg (fun v : H => ‖v‖ ^ 2) h_split
    _ = ‖Gap N ψ‖ ^ 2 + ‖(1 - Gap N) ψ‖ ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      exact h_pyth

/-- The anomaly preserves the norm of a vector exactly when that vector is
already in the support of the regular gap projection. -/
theorem regular_anomaly_norm_saturation_iff_gap_fixed (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    ‖Sigma N ψ‖ = ‖ψ‖ ↔ Gap N ψ = ψ := by
  rw [← regular_gap_norm_eq_anomaly_norm N h_nil h_reg ψ]
  constructor
  · intro h_norm
    have h_pyth := regular_gap_pythagorean_decomposition N h_nil h_reg ψ
    have h_comp_sq : ‖(1 - Gap N) ψ‖ ^ 2 = 0 := by
      rw [h_norm] at h_pyth
      nlinarith [h_pyth]
    have h_comp_norm : ‖(1 - Gap N) ψ‖ = 0 := by
      nlinarith [h_comp_sq, sq_nonneg (‖(1 - Gap N) ψ‖ : ℝ)]
    have h_comp : (1 - Gap N) ψ = 0 := norm_eq_zero.mp h_comp_norm
    have h_split : ψ = Gap N ψ + (1 - Gap N) ψ := by
      change ψ = Gap N ψ + (ψ - Gap N ψ)
      calc ψ = (ψ - Gap N ψ) + Gap N ψ := (sub_add_cancel ψ (Gap N ψ)).symm
        _ = Gap N ψ + (ψ - Gap N ψ) := add_comm _ _
    rw [h_comp, add_zero] at h_split
    exact h_split.symm
  · intro h_fixed
    exact congrArg (fun v : H => ‖v‖) h_fixed

/-- The regular anomaly support projection is contractive on vectors. -/
theorem regular_gap_nonexpansive (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    ‖Gap N ψ‖ ≤ ‖ψ‖ := by
  have h := regular_gap_pythagorean_decomposition N h_nil h_reg ψ
  nlinarith [sq_nonneg (‖(1 - Gap N) ψ‖ : ℝ),
    norm_nonneg (Gap N ψ), norm_nonneg ψ]

/-- The operator norm of the regular anomaly support projection is at most
one. -/
theorem regular_gap_opNorm_le_one (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    ‖Gap N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (Gap N) zero_le_one
  intro ψ
  simpa using regular_gap_nonexpansive N h_nil h_reg ψ

/-- A nonzero regular nilpotent channel has a nonzero support projection;
its projection norm is therefore exactly one. -/
theorem regular_gap_opNorm_eq_one_of_ne_zero (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (hN : N ≠ 0) :
    ‖Gap N‖ = 1 := by
  have h_fix : Gap N * N = N := Gap_mul_N_plus N h_nil h_reg
  have hN_norm : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have h_lower_mul : (1 : ℝ) * ‖N‖ ≤ ‖Gap N‖ * ‖N‖ := by
    calc (1 : ℝ) * ‖N‖ = ‖N‖ := one_mul _
      _ = ‖Gap N * N‖ := by rw [h_fix]
      _ ≤ ‖Gap N‖ * ‖N‖ := norm_mul_le _ _
  have h_lower : 1 ≤ ‖Gap N‖ :=
    le_of_mul_le_mul_right h_lower_mul hN_norm
  exact le_antisymm (regular_gap_opNorm_le_one N h_nil h_reg) h_lower

/-- The imaginary multiple of the symmetric chiral block is skew-adjoint. -/
theorem imaginaryPhi_skewAdjoint (N : EndH) :
    ContinuousLinearMap.adjoint (Complex.I • Phi N) = -(Complex.I • Phi N) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp [Phi, star_add, add_comm]

/-- The chiral rotor is skew-adjoint. -/
theorem J_skewAdjoint (N : EndH) :
    ContinuousLinearMap.adjoint (J N) = -J N := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp [J, sub_eq_add_neg, add_comm]

/-- The commutator of the two skew-adjoint chiral generators is the parity
anomaly multiplied by `-2i`: `[i Φ, J] = -2i Σ`. -/
theorem imaginaryPhi_commutator_eq_anomaly (N : EndH)
    (h_nil : N * N = 0) :
    opCommutator (Complex.I • Phi N) (J N) =
      ((-2 : ℂ) * Complex.I) • Sigma N := by
  have h_star_nil : star N * star N = 0 := by
    exact star_N_plus_sq N h_nil
  have h_phi_j : Phi N * J N = -Sigma N := by
    change (N + star N) * (N - star N) =
      -(N * star N - star N * N)
    rw [add_mul, mul_sub, mul_sub, h_nil, h_star_nil]
    abel
  have h_j_phi : J N * Phi N = Sigma N := by
    exact J_mul_Phi N h_nil
  have h_comm : opCommutator (Complex.I • Phi N) (J N) =
      Complex.I • (Phi N * J N - J N * Phi N) := by
    ext x
    change (Complex.I • Phi N) (J N x) -
        J N (Complex.I • Phi N x) =
      Complex.I • (Phi N (J N x) - J N (Phi N x))
    simp only [smul_apply, map_smul]
    rw [smul_sub]
  rw [h_comm, h_phi_j, h_j_phi]
  have h_scalar : Complex.I • (-Sigma N - Sigma N) =
      ((-2 : ℂ) * Complex.I) • Sigma N := by
    module
  rw [h_scalar]

/-- On a normalized state, the Berry curvature of `(i Φ, J)` is exactly twice
the expectation of the parity anomaly, with the sign fixed by the commutator
convention used in `opCommutator`. -/
theorem berryCurvature_eq_neg_two_anomaly_expectation (N : EndH)
    (h_nil : N * N = 0) (ψ : NormalizedState H) :
    (berryCurvature ψ (Complex.I • Phi N) (J N) : ℂ) * Complex.I =
      ((-2 : ℂ) * Complex.I) * inner ℂ ψ.vec (Sigma N ψ.vec) := by
  rw [berryCurvature_skewAdjoint_commutator ψ (Complex.I • Phi N) (J N)
    (imaginaryPhi_skewAdjoint N) (J_skewAdjoint N),
    imaginaryPhi_commutator_eq_anomaly N h_nil]
  simp [inner_smul_right]

/-- Robertson's bound for the chiral pair controls the parity-anomaly
expectation. No spectral interpretation of this scalar bound is assumed. -/
theorem chiral_anomaly_robertson_bound (N : EndH)
    (ψ : NormalizedState H) :
    fubiniStudyMetric ψ (Complex.I • Phi N) (Complex.I • Phi N) *
      fubiniStudyMetric ψ (J N) (J N) ≥
        (1 / 4 : ℝ) *
          (berryCurvature ψ (Complex.I • Phi N) (J N)) ^ 2 := by
  exact berry_curvature_uncertainty_bound ψ (Complex.I • Phi N) (J N)

/-- Robertson's commutator form gives a bound directly on the norm square of
the parity-anomaly expectation. The factor `1/4` cancels the squared `2i`
coefficient in `[i Φ, J] = -2i Σ`. -/
theorem chiral_anomaly_expectation_norm_bound (N : EndH)
    (h_nil : N * N = 0) (ψ : NormalizedState H) :
    fubiniStudyMetric ψ (Complex.I • Phi N) (Complex.I • Phi N) *
      fubiniStudyMetric ψ (J N) (J N) ≥
        Complex.normSq (inner ℂ ψ.vec (Sigma N ψ.vec)) := by
  have h_bound :=
    InfoGeometry.QuantumGeometry.TensorBridge.robertson_schrodinger_full_uncertainty
      ψ (Complex.I • Phi N) (J N)
      (imaginaryPhi_skewAdjoint N) (J_skewAdjoint N)
  have h_norm :
      Complex.normSq
        (inner ℂ ψ.vec (opCommutator (Complex.I • Phi N) (J N) ψ.vec)) =
        4 * Complex.normSq (inner ℂ ψ.vec (Sigma N ψ.vec)) := by
    rw [imaginaryPhi_commutator_eq_anomaly N h_nil]
    rw [smul_apply, inner_smul_right, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_I]
    simp only [mul_one]
    have h_neg_two : Complex.normSq (-2 : ℂ) = 4 := by
      norm_num [Complex.normSq]
    rw [h_neg_two, mul_comm]
  have h_ineq := h_bound.2
  rw [h_norm] at h_ineq
  nlinarith [h_ineq]

end InfoGeometry.QuantumGeometry.ChiralAnomalyRobertsonBridge
