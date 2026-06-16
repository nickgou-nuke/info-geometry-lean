import Mathlib
import InfoGeometry.Algebra.CuntzContractionLemmas
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz Hamiltonian is diagonal in the Pierce decomposition

P_i H P_j = δ_{ij} ε_i P_i

Proved using the contraction lemmas (right_contract, left_contract).
This is the core identity for the primon gas: the Hamiltonian
commutes with all projectors and has eigenvalues ε_i on each P_i.
-/
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzContractionLemmas
open InfoGeometry.Algebra.CuntzPrimonHamiltonian

noncomputable section

namespace InfoGeometry.Algebra.CuntzHamiltonianDiagonal

/-- P_i H P_j = 0 for i≠j (off-diagonal vanishes). -/
theorem hamiltonian_off_diag (n : ℕ) (ε : Fin n → ℂ) (i j : Fin n) (hij : i ≠ j) :
    (cuntzS n i * cuntzSdag n i) * (hamiltonian n ε) *
    (cuntzS n j * cuntzSdag n j) = 0 := by
  dsimp [hamiltonian]
  -- P_i (Σ_k ε_k P_k) P_j = Σ_k ε_k P_i P_k P_j
  -- P_i P_k = 0 for k≠i. P_k P_j = 0 for k≠j.
  -- So the sum reduces to the k=i AND k=j term. But i≠j, so no term survives.
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
  -- Goal: Σ_k ε_k • P_i P_k P_j = 0
  refine Finset.sum_eq_zero (λ k _ => ?_)
  by_cases hki : k = i
  · subst k; simp [cuntz_range_projector n i, cuntz_range_projectors_orthogonal n hij,
      mul_assoc]
  · simp [cuntz_range_projectors_orthogonal n (Ne.symm hki), mul_assoc]

/-- P_i H P_i = ε_i P_i (diagonal term). -/
theorem hamiltonian_diag (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (hamiltonian n ε) *
    (cuntzS n i * cuntzSdag n i) = ε i • (cuntzS n i * cuntzSdag n i) := by
  dsimp [hamiltonian]
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
  -- Goal: Σ_k ε_k • P_i P_k P_i = ε_i • P_i
  -- For k=i: P_i P_i P_i = P_i. For k≠i: P_i P_k = 0 causing P_i P_k P_i = 0.
  rw [Finset.sum_eq_single i (M := CuntzAlg n) (λ k _ hki => ?_) (λ hi => ?_)]
  · simp [cuntz_range_projector n i, mul_assoc]
  · simp [cuntz_range_projectors_orthogonal n (Ne.symm hki), mul_assoc]
  · exact (Finset.not_mem_univ i hi).elim

/-- The Hamiltonian is diagonal in the projector basis:
    H = Σ_i ε_i P_i, and P_i H P_j = δ_{ij} ε_i P_i. -/
theorem hamiltonian_diagonalization (n : ℕ) (ε : Fin n → ℂ) (i j : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (hamiltonian n ε) *
    (cuntzS n j * cuntzSdag n j) =
    (if i = j then ε i • (cuntzS n i * cuntzSdag n i) else 0) := by
  by_cases hij : i = j
  · subst j; rw [hamiltonian_diag n ε i]; simp
  · rw [hamiltonian_off_diag n ε i j hij]; simp [hij]

/-- The Hamiltonian commutes with each range projector:
    H P_i = P_i H = ε_i P_i. -/
theorem hamiltonian_commutes_projector (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    hamiltonian n ε * (cuntzS n i * cuntzSdag n i) =
    (cuntzS n i * cuntzSdag n i) * hamiltonian n ε := by
  -- Both sides equal ε_i P_i:
  rw [H_mul_P n ε i, P_mul_H n ε i]

end InfoGeometry.Algebra.CuntzHamiltonianDiagonal
