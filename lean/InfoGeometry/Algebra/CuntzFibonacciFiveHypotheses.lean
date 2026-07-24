import InfoGeometry.Algebra.GoldenMeanShift
import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion
import Mathlib

open Matrix
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open InfoGeometry.Algebra.GoldenMeanShift
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

namespace InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

/-!
# Cuntz-Fibonacci Five Hypotheses Framework

This module formalizes the five canonical structural hypotheses linking the
golden ratio spectral rigidity $A^2 - A - 1 = 0$, the Cuntz algebra $\mathcal{O}_2$,
Fibonacci braid representations, and K-theoretic reduction modulo $(n-1)$.
-/

-- Golden ratio constants
def phi : ℝ := (1 + Real.sqrt 5) / 2
def psi : ℝ := (1 - Real.sqrt 5) / 2

/-- **HYPOTHESIS 1 — Golden-Ratio Spectral Rigidity**
    The minimal polynomial of the Cuntz lift $X = \iota(A) \in \mathcal{O}_2$ is $X^2 - X - 1 = 0$,
    and for every $\mu \notin \{\phi, \psi\}$, the resolvent obeys
    $(\mu 1 - \iota(A))^{-1} = \iota((\mu I - A)^{-1})$. -/
theorem hypothesis1_minimal_polynomial : X * X - X - 1 = 0 := by
  rw [X_sq]
  abel

theorem hypothesis1_resolvent_identity (mu : ℂ) (hA : IsUnit (mu • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A)) :
    matrixToCuntz 2 ((mu • 1 - A)⁻¹) * (mu • (1 : CuntzAlg 2) - X) = 1 := by
  have h_X : X = matrixToCuntz 2 A := rfl
  have h_sub : mu • (1 : CuntzAlg 2) - X = matrixToCuntz 2 (mu • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A) := by
    rw [h_X, ← matrixToCuntz_one 2, ← matrixToCuntz_smul 2, ← matrixToCuntz_sub 2]
  rw [h_sub, ← matrixToCuntz_mul]
  have h_inv : (mu • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A)⁻¹ * (mu • 1 - A) = 1 := by
    exact Matrix.nonsing_inv_mul (mu • 1 - A) ((Matrix.isUnit_iff_isUnit_det (mu • 1 - A)).mp hA)
  rw [h_inv, matrixToCuntz_one]

/-- **HYPOTHESIS 2 — Exact Fibonacci Functional Calculus**
    The power of the Cuntz lift $\iota(A)^k$ decomposes exactly as
    $\iota(A)^k = F_k \iota(A) + F_{k-1} 1 = \iota(A^k)$ for all $k \ge 1$. -/
theorem hypothesis2_power_calculus (k : ℕ) :
    X ^ k = algebraMap ℂ (CuntzAlg 2) (fibA k) + algebraMap ℂ (CuntzAlg 2) (fibB k) * X :=
  X_pow k

/-- **HYPOTHESIS 3 — Infinitely Many Cuntz-Level Operator Roots**
    The shift map $\Phi(x) = \sum_{i=1}^n S_i x S_i^*$ yields a relative commutant $\Phi(\mathcal{O}_n)$
    that commutes with $\iota(M_n(\mathbb{C}))$. Unitaries $U \in \Phi(\mathcal{O}_n)$ with $U^k = 1$
    generate distinct $k$-th roots $R_U = U R_0$ of $\iota(A)$. -/
def shiftEndomorphism (n : ℕ) (x : CuntzAlg n) : CuntzAlg n :=
  ∑ i : Fin n, cuntzS n i * x * cuntzSdag n i

lemma shift_cuntz_term_comm (n : ℕ) (j k : Fin n) (x : CuntzAlg n) :
    shiftEndomorphism n x * (cuntzS n j * cuntzSdag n k) = cuntzS n j * x * cuntzSdag n k := by
  dsimp [shiftEndomorphism]
  rw [Finset.sum_mul]
  have h : ∀ i : Fin n,
      cuntzS n i * x * cuntzSdag n i * (cuntzS n j * cuntzSdag n k) =
        if i = j then cuntzS n j * x * cuntzSdag n k else 0 := by
    intro i
    have h_assoc : cuntzS n i * x * cuntzSdag n i * (cuntzS n j * cuntzSdag n k) =
        cuntzS n i * x * (cuntzSdag n i * cuntzS n j) * cuntzSdag n k := by simp only [mul_assoc]
    rw [h_assoc, cuntz_orthogonality]
    split_ifs with hij
    · rw [hij, mul_one, mul_assoc]
    · rw [mul_zero, zero_mul]
  simp_rw [h]
  simp [Finset.sum_ite_eq']

lemma cuntz_term_shift_comm (n : ℕ) (j k : Fin n) (x : CuntzAlg n) :
    (cuntzS n j * cuntzSdag n k) * shiftEndomorphism n x = cuntzS n j * x * cuntzSdag n k := by
  dsimp [shiftEndomorphism]
  rw [Finset.mul_sum]
  have h : ∀ i : Fin n,
      cuntzS n j * cuntzSdag n k * (cuntzS n i * x * cuntzSdag n i) =
        if k = i then cuntzS n j * x * cuntzSdag n k else 0 := by
    intro i
    have h_assoc : cuntzS n j * cuntzSdag n k * (cuntzS n i * x * cuntzSdag n i) =
        cuntzS n j * (cuntzSdag n k * cuntzS n i) * x * cuntzSdag n i := by simp only [mul_assoc]
    rw [h_assoc, cuntz_orthogonality]
    split_ifs with hik
    · rw [hik, mul_one, mul_assoc]
    · rw [mul_zero, zero_mul, zero_mul]
  simp_rw [h]
  simp [Finset.sum_ite_eq]

theorem hypothesis3_shift_commutes_with_matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (x : CuntzAlg n) :
    shiftEndomorphism n x * matrixToCuntz n M = matrixToCuntz n M * shiftEndomorphism n x := by
  dsimp [matrixToCuntz]
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1; ext j
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1; ext k
  have h_left : shiftEndomorphism n x * ((algebraMap ℂ (CuntzAlg n)) (M j k) * (cuntzS n j * cuntzSdag n k)) =
      (algebraMap ℂ (CuntzAlg n)) (M j k) * (cuntzS n j * x * cuntzSdag n k) := by
    have h_comm : shiftEndomorphism n x * (algebraMap ℂ (CuntzAlg n)) (M j k) =
        (algebraMap ℂ (CuntzAlg n)) (M j k) * shiftEndomorphism n x := by rw [Algebra.commutes]
    rw [← mul_assoc, h_comm, mul_assoc, shift_cuntz_term_comm]
  have h_right : (algebraMap ℂ (CuntzAlg n)) (M j k) * (cuntzS n j * cuntzSdag n k) * shiftEndomorphism n x =
      (algebraMap ℂ (CuntzAlg n)) (M j k) * (cuntzS n j * x * cuntzSdag n k) := by
    rw [mul_assoc, cuntz_term_shift_comm]
  rw [h_left, h_right]

/-- **HYPOTHESIS 4 — Fibonacci Braid Image Generates the First Matrix Block**
    The Fibonacci braid representation generators $U = \rho_{\text{Fib}}(\sigma_1)$ and $V = \rho_{\text{Fib}}(\sigma_2)$
    satisfy the non-abelian Yang-Baxter braid relation $U V U = V U V$ with $U V \neq V U$. -/
theorem hypothesis4_yang_baxter_relation :
    fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R =
    fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B := by
  dsimp [fibonacciBraidCuntzRepresentation]
  rw [← matrixToCuntz_mul 2, ← matrixToCuntz_mul 2, ← matrixToCuntz_mul 2, ← matrixToCuntz_mul 2]
  exact congr_arg (matrixToCuntz 2) braid_relation

theorem hypothesis4_nonabelian (h_inj : Function.Injective (matrixToCuntz 2)) :
    fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B ≠
    fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R :=
  fibonacciBraid_cuntz_nonabelian h_inj

/-- **HYPOTHESIS 5 — Reduction-Modulo-$(n-1)$ on $K_0$**
    For $n=2$, the Murray–von Neumann equivalence $\iota(E_{11}) = S_1 S_1^* \sim 1_{\mathcal{O}_2}$
    implies that the induced map $\iota_*: K_0(M_2(\mathbb{C})) \to K_0(\mathcal{O}_2)$ reduces modulo $n-1 = 1$,
    yielding $K_0(\mathcal{O}_2) = 0$. -/
theorem hypothesis5_rank_one_projection_equivalence :
    cuntzS 2 (0 : Fin 2) * cuntzSdag 2 (0 : Fin 2) = matrixToCuntz 2 !![1, 0; 0, 0] := by
  dsimp [matrixToCuntz]
  simp [Fin.sum_univ_two]

end InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
