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

/-- Positivity of the anomaly-square gap on every Hilbert-space vector. -/
theorem gap_expectation_nonneg (N : EndH) (ψ : H) :
    0 ≤ (inner ℂ ψ (Gap N ψ)).re := by
  rw [gap_expectation_eq_anomaly_norm_sq]
  exact sq_nonneg _

/-- The anomaly-square operator is self-adjoint. -/
theorem Gap_selfAdjoint (N : EndH) : star (Gap N) = Gap N := by
  simp [Gap, star_mul, Sigma_selfAdjoint]

/-- When the chiral anomaly is a regular nilpotent pair, `Gap` is idempotent
and its state expectation is the squared norm of the projected state. -/
theorem regular_gap_expectation_eq_norm_sq (N : EndH)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) (ψ : H) :
    (inner ℂ ψ (Gap N ψ)).re = ‖Gap N ψ‖ ^ 2 := by
  have h_adj : ContinuousLinearMap.adjoint (Gap N) = Gap N := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact Gap_selfAdjoint N
  have h_inner := adjoint_inner_right (Gap N) ψ (Gap N ψ)
  rw [h_adj, ← Gap_idem N h_nil h_reg] at h_inner
  change (inner ℂ ψ (Gap N (Gap N ψ))).re = ‖Gap N ψ‖ ^ 2
  rw [h_inner, inner_self_eq_norm_sq_to_K]
  change (Complex.ofReal (‖Gap N ψ‖) ^ 2).re = ‖Gap N ψ‖ ^ 2
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re _

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
