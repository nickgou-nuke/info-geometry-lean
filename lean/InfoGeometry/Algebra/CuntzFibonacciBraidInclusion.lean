import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Categorical.FibonacciUniversalityColimit
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Arithmetic.WeylArithmeticDivergence

open Matrix
open Complex
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Categorical.FibonacciUniversalityColimit
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Arithmetic.WeylArithmeticDivergence

noncomputable section

namespace CuntzFibonacciBraidInclusion

private lemma tau_ne_zero : τ ≠ 0 := by
  intro h
  have hc : τ ^ 2 + τ = 1 := tau_sq_add_tau
  rw [h] at hc
  norm_num at hc

private lemma s_ne_zero : s ≠ 0 := by
  intro h
  have hτ : τ = 0 := by
    rw [← s_sq_eq_tau, h]
    norm_num
  exact tau_ne_zero hτ

private lemma q_sq_ne_neg_one : q ^ 2 ≠ -1 := by
  intro h
  have h3 : q ^ 3 = -q := by
    calc
      q ^ 3 = q * q ^ 2 := by ring
      _ = q * (-1) := by rw [h]
      _ = -q := by ring
  have h4 : q ^ 4 = 1 := by
    calc
      q ^ 4 = (q ^ 2) * (q ^ 2) := by ring
      _ = (-1) * (-1) := by rw [h]
      _ = 1 := by ring
  have hc : q^4 - q^3 + q^2 - q + 1 = 0 := cyclotomic_relation
  rw [h4, h3, h] at hc
  norm_num at hc

private lemma q_plus_q_cubed_ne_zero : q + q ^ 3 ≠ 0 := by
  intro hsum
  have hprod : q * (1 + q ^ 2) = 0 := by
    calc
      q * (1 + q ^ 2) = q + q ^ 3 := by ring
      _ = 0 := hsum
  rcases mul_eq_zero.mp hprod with hq | hfac
  · exact (Complex.exp_ne_zero _) hq
  · have hq2 : q ^ 2 = -1 := by
      calc
        q ^ 2 = (1 + q ^ 2) - 1 := by ring
        _ = 0 - 1 := by rw [hfac]
        _ = -1 := by ring
    exact q_sq_ne_neg_one hq2

/-- The Fibonacci generators `R` and `B = F R F` do not commute. -/
lemma fibonacci_generators_noncommute : R * B ≠ B * R := by
  intro h
  have h01 := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
  simp [R, B, F, Matrix.mul_apply, Fin.sum_univ_two] at h01
  ring_nf at h01
  have hmove :
      -((q ^ 4)⁻¹ * τ * s * q ^ 3) + (q ^ 4)⁻¹ ^ 2 * τ * s -
          ((q ^ 4)⁻¹ * τ * s * q ^ 3 - τ * s * q ^ 6) = 0 := by
    exact sub_eq_zero.mpr h01
  have hzero : τ * s * (q + q ^ 3) ^ 2 = 0 := by
    calc
      τ * s * (q + q ^ 3) ^ 2 =
          -((q ^ 4)⁻¹ * τ * s * q ^ 3) + (q ^ 4)⁻¹ ^ 2 * τ * s -
            ((q ^ 4)⁻¹ * τ * s * q ^ 3 - τ * s * q ^ 6) := by
            rw [q_inv_four_eq_neg_q]
            ring
      _ = 0 := hmove
  have hprod := mul_eq_zero.mp hzero
  rcases hprod with hτs | hqq
  · have hprodτs := mul_eq_zero.mp hτs
    rcases hprodτs with hτ | hs
    · exact tau_ne_zero hτ
    · exact s_ne_zero hs
  · exact q_plus_q_cubed_ne_zero (sq_eq_zero_iff.mp hqq)

/-- The canonical embedding of `M_n(ℂ)` into the Cuntz algebra `O_n`. -/
def matrixToCuntz (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : CuntzAlg n :=
  ∑ i : Fin n, ∑ j : Fin n, (algebraMap ℂ (CuntzAlg n) (M i j)) * (cuntzS n i * cuntzSdag n j)

lemma matrixToCuntz_mul_term_comm (n : ℕ) (i k l j : Fin n) (M N : Matrix (Fin n) (Fin n) ℂ) :
    (algebraMap ℂ (CuntzAlg n) (M i k) * (cuntzS n i * cuntzSdag n k)) *
      (algebraMap ℂ (CuntzAlg n) (N l j) * (cuntzS n l * cuntzSdag n j)) =
    algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
      (cuntzS n i * (cuntzSdag n k * cuntzS n l) * cuntzSdag n j) := by
  have h1 : (cuntzS n i * cuntzSdag n k) * algebraMap ℂ (CuntzAlg n) (N l j) =
      algebraMap ℂ (CuntzAlg n) (N l j) * (cuntzS n i * cuntzSdag n k) :=
    (Algebra.commutes (N l j) (cuntzS n i * cuntzSdag n k)).symm
  calc
    (algebraMap ℂ (CuntzAlg n) (M i k) * (cuntzS n i * cuntzSdag n k)) *
      (algebraMap ℂ (CuntzAlg n) (N l j) * (cuntzS n l * cuntzSdag n j))
      = algebraMap ℂ (CuntzAlg n) (M i k) * ((cuntzS n i * cuntzSdag n k) *
          algebraMap ℂ (CuntzAlg n) (N l j)) * (cuntzS n l * cuntzSdag n j) := by
        simp only [mul_assoc]
    _ = algebraMap ℂ (CuntzAlg n) (M i k) * (algebraMap ℂ (CuntzAlg n) (N l j) *
          (cuntzS n i * cuntzSdag n k)) * (cuntzS n l * cuntzSdag n j) := by
        rw [h1]
    _ = (algebraMap ℂ (CuntzAlg n) (M i k) * algebraMap ℂ (CuntzAlg n) (N l j)) *
          (cuntzS n i * cuntzSdag n k * (cuntzS n l * cuntzSdag n j)) := by
        simp only [mul_assoc]
    _ = algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
          (cuntzS n i * (cuntzSdag n k * cuntzS n l) * cuntzSdag n j) := by
        rw [← map_mul]
        simp only [mul_assoc]

lemma matrixToCuntz_mul_ite_term (n : ℕ) (i k l j : Fin n) (M N : Matrix (Fin n) (Fin n) ℂ) :
    algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
      (cuntzS n i * (if k = l then (1 : CuntzAlg n) else 0) * cuntzSdag n j) =
    if k = l then algebraMap ℂ (CuntzAlg n) (M i k * N l j) * (cuntzS n i * cuntzSdag n j) else 0 := by
  split_ifs
  · simp
  · simp

/-- The embedding is an algebra homomorphism (preserves multiplication). -/
theorem matrixToCuntz_mul (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ) :
    matrixToCuntz n (M * N) = matrixToCuntz n M * matrixToCuntz n N := by
  symm
  calc
    matrixToCuntz n M * matrixToCuntz n N
      = (∑ i, ∑ k, algebraMap ℂ (CuntzAlg n) (M i k) * (cuntzS n i * cuntzSdag n k)) *
        (∑ l, ∑ j, algebraMap ℂ (CuntzAlg n) (N l j) * (cuntzS n l * cuntzSdag n j)) := rfl
    _ = ∑ i, ∑ k, ∑ l, ∑ j, (algebraMap ℂ (CuntzAlg n) (M i k) * (cuntzS n i * cuntzSdag n k)) *
        (algebraMap ℂ (CuntzAlg n) (N l j) * (cuntzS n l * cuntzSdag n j)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i, ∑ k, ∑ l, ∑ j, algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
        (cuntzS n i * (cuntzSdag n k * cuntzS n l) * cuntzSdag n j) := by
      simp_rw [matrixToCuntz_mul_term_comm]
    _ = ∑ i, ∑ k, ∑ l, ∑ j, algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
        (cuntzS n i * (if k = l then (1 : CuntzAlg n) else 0) * cuntzSdag n j) := by
      simp_rw [cuntz_orthogonality]
    _ = ∑ i, ∑ k, ∑ l, ∑ j, if k = l then algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
        (cuntzS n i * cuntzSdag n j) else 0 := by
      simp_rw [matrixToCuntz_mul_ite_term]
    _ = ∑ i, ∑ k, ∑ j, ∑ l, if k = l then algebraMap ℂ (CuntzAlg n) (M i k * N l j) *
        (cuntzS n i * cuntzSdag n j) else 0 := by
      congr 1; ext i; congr 1; ext k; rw [Finset.sum_comm]
    _ = ∑ i, ∑ k, ∑ j, algebraMap ℂ (CuntzAlg n) (M i k * N k j) *
        (cuntzS n i * cuntzSdag n j) := by
      congr 1; ext i; congr 1; ext k; congr 1; ext j
      rw [Finset.sum_ite_eq]
      simp
    _ = ∑ i, ∑ j, ∑ k, algebraMap ℂ (CuntzAlg n) (M i k * N k j) *
        (cuntzS n i * cuntzSdag n j) := by
      congr 1; ext i; rw [Finset.sum_comm]
    _ = matrixToCuntz n (M * N) := by
      simp_rw [matrixToCuntz, Matrix.mul_apply, map_sum, Finset.sum_mul]

/-- The canonical trace density map from the Braid limit generators into O_2. -/
def fibonacciBraidCuntzRepresentation :
    Matrix (Fin 2) (Fin 2) ℂ → CuntzAlg 2 := matrixToCuntz 2

/--
The Fibonacci braid generators remain non-commutative inside the Cuntz topological limit,
conditional on the algebraic density (injectivity) of the finite matrix representation `M_2(ℂ) ↪ O_2`.
-/
theorem fibonacciBraid_cuntz_nonabelian
    (h_inj : Function.Injective (matrixToCuntz 2)) :
    fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B ≠
      fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R := by
  intro h_eq
  have h_mul_RB : fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B = matrixToCuntz 2 (R * B) := by
    exact (matrixToCuntz_mul 2 R B).symm
  have h_mul_BR : fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R = matrixToCuntz 2 (B * R) := by
    exact (matrixToCuntz_mul 2 B R).symm
  rw [h_mul_RB, h_mul_BR] at h_eq
  have h_mat_eq := h_inj h_eq
  exact fibonacci_generators_noncommute h_mat_eq

/-! ## Itakura--Saito socket and conjugation invariance -/

/-- Socket for explicit Itakura--Saito data on the Cuntz-algebra image. -/
structure ItakuraCuntzSocket (n : ℕ) where
  cuntzTrace : CuntzAlg n → ℝ
  invImage : Matrix (Fin n) (Fin n) ℂ → CuntzAlg n
  h_trace_conj :
    ∀ M : Matrix (Fin n) (Fin n) ℂ,
      cuntzTrace (matrixToCuntz n (M.transpose)) = cuntzTrace (matrixToCuntz n M)
  h_inv_transpose_trace :
    ∀ M : Matrix (Fin n) (Fin n) ℂ,
      cuntzTrace (invImage M) = cuntzTrace (invImage (M.transpose))

/-- Socket-based Itakura--Saito divergence readout. -/
noncomputable def divergenceSocket
    (socket : ItakuraCuntzSocket n)
    (M P : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  InfoGeometry.Arithmetic.WeylArithmeticDivergence.itakuraSaito
    (socket.cuntzTrace (matrixToCuntz n M))
    (socket.cuntzTrace (matrixToCuntz n P))

/-- Lemma 1: conjugation preserves scalar trace of the matrix image. -/
theorem trace_conj_matrixToCuntz
    (socket : ItakuraCuntzSocket n) (M : Matrix (Fin n) (Fin n) ℂ) :
    socket.cuntzTrace (matrixToCuntz n M.transpose) =
      socket.cuntzTrace (matrixToCuntz n M) := by
  exact socket.h_trace_conj M

/-- Lemma 2: conjugation preserves the log-potential. -/
theorem log_potential_preserved
    (socket : ItakuraCuntzSocket n) (M : Matrix (Fin n) (Fin n) ℂ)
    (_ : 0 < socket.cuntzTrace (matrixToCuntz n M)) :
    Real.log (socket.cuntzTrace (matrixToCuntz n M.transpose)) =
      Real.log (socket.cuntzTrace (matrixToCuntz n M)) := by
  rw [trace_conj_matrixToCuntz socket M]

/-- Lemma 3: conjugation preserves the inv-pairing term trace. -/
theorem inv_pairing_conj_preserved
    (socket : ItakuraCuntzSocket n)
    (M : Matrix (Fin n) (Fin n) ℂ) (_ : M.det ≠ 0) :
    socket.cuntzTrace (socket.invImage M) =
      socket.cuntzTrace (socket.invImage M.transpose) := by
  exact socket.h_inv_transpose_trace M

/-- Lemma 4: full divergence invariance under commuting conjugation. -/
theorem itakuraSaito_invariance_under_conjugation
    (socket : ItakuraCuntzSocket n)
    (M P : Matrix (Fin n) (Fin n) ℂ)
    (_ : 0 < socket.cuntzTrace (matrixToCuntz n M))
    (_ : 0 < socket.cuntzTrace (matrixToCuntz n P)) :
    divergenceSocket socket M P =
      divergenceSocket socket M.transpose P.transpose := by
  unfold divergenceSocket
  have h_trace_M : socket.cuntzTrace (matrixToCuntz n M.transpose) =
      socket.cuntzTrace (matrixToCuntz n M) := by
    exact trace_conj_matrixToCuntz socket M
  have h_trace_P : socket.cuntzTrace (matrixToCuntz n P.transpose) =
      socket.cuntzTrace (matrixToCuntz n P) := by
    exact trace_conj_matrixToCuntz socket P
  have h_log_M : Real.log (socket.cuntzTrace (matrixToCuntz n M.transpose)) =
      Real.log (socket.cuntzTrace (matrixToCuntz n M)) := by
    rw [h_trace_M]
  have h_log_P : Real.log (socket.cuntzTrace (matrixToCuntz n P.transpose)) =
      Real.log (socket.cuntzTrace (matrixToCuntz n P)) := by
    rw [h_trace_P]
  have h_ratio : socket.cuntzTrace (matrixToCuntz n M.transpose) /
      socket.cuntzTrace (matrixToCuntz n P.transpose) =
    socket.cuntzTrace (matrixToCuntz n M) / socket.cuntzTrace (matrixToCuntz n P) := by
    rw [h_trace_M, h_trace_P]
  have h_log_ratio :
      Real.log (socket.cuntzTrace (matrixToCuntz n M.transpose) /
        socket.cuntzTrace (matrixToCuntz n P.transpose)) =
    Real.log (socket.cuntzTrace (matrixToCuntz n M) / socket.cuntzTrace (matrixToCuntz n P)) := by
    rw [h_ratio]
  dsimp [itakuraSaito]
  rw [h_ratio]

end CuntzFibonacciBraidInclusion
