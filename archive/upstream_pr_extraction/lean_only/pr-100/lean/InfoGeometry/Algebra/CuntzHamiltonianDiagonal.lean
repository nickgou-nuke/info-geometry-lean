import Mathlib.Tactic
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
  change P n i * hamiltonian n ε * P n j = 0
  calc
    P n i * hamiltonian n ε * P n j = P n i * (hamiltonian n ε * P n j) := by
      rw [mul_assoc]
    _ = P n i * (ε j • P n j) := by
      rw [H_mul_P n ε j]
    _ = ε j • (P n i * P n j) := by
      rw [mul_smul_comm]
    _ = 0 := by
      rw [P_ortho n hij]
      simp

/-- P_i H P_i = ε_i P_i (diagonal term). -/
theorem hamiltonian_diag (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (hamiltonian n ε) *
    (cuntzS n i * cuntzSdag n i) = ε i • (cuntzS n i * cuntzSdag n i) := by
  change P n i * hamiltonian n ε * P n i = ε i • P n i
  calc
    P n i * hamiltonian n ε * P n i = P n i * (hamiltonian n ε * P n i) := by
      rw [mul_assoc]
    _ = P n i * (ε i • P n i) := by
      rw [H_mul_P n ε i]
    _ = ε i • (P n i * P n i) := by
      rw [mul_smul_comm]
    _ = ε i • P n i := by
      rw [P_idem n i]

/-- The Hamiltonian is diagonal in the projector basis:
    H = Σ_i ε_i P_i, and P_i H P_j = δ_{ij} ε_i P_i. -/
theorem hamiltonian_diagonalization (n : ℕ) (ε : Fin n → ℂ) (i j : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (hamiltonian n ε) *
    (cuntzS n j * cuntzSdag n j) =
    (if i = j then ε i • (cuntzS n i * cuntzSdag n i) else 0) := by
  by_cases hij : i = j
  · subst j; rw [hamiltonian_diag n ε i]; simp
  · rw [hamiltonian_off_diag n ε i j hij]; simp [hij]

theorem hamiltonian_pow_diagonalization
    (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) (i j : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (hamiltonian n ε) ^ k *
        (cuntzS n j * cuntzSdag n j) =
      (if i = j then (ε i) ^ k • (cuntzS n i * cuntzSdag n i) else 0) := by
  change P n i * (hamiltonian n ε) ^ k * P n j = _
  by_cases hij : i = j
  · subst j
    calc
      P n i * (hamiltonian n ε) ^ k * P n i =
          (P n i * (hamiltonian n ε) ^ k) * P n i := by
            rw [mul_assoc]
      _ = ((ε i) ^ k • P n i) * P n i := by
            rw [P_mul_H_pow]
      _ = (ε i) ^ k • P n i := by
            rw [smul_mul_assoc, P_idem]
      _ = if i = i then (ε i) ^ k • (cuntzS n i * cuntzSdag n i) else 0 := by
            simp [P]
  · calc
      P n i * (hamiltonian n ε) ^ k * P n j =
          (P n i * (hamiltonian n ε) ^ k) * P n j := by
            rw [mul_assoc]
      _ = ((ε i) ^ k • P n i) * P n j := by
            rw [P_mul_H_pow]
      _ = 0 := by
            rw [smul_mul_assoc, P_ortho n hij, smul_zero]
      _ = if i = j then (ε i) ^ k • P n i else 0 := by
            simp [hij]

/-- The Hamiltonian commutes with each range projector:
    H P_i = P_i H = ε_i P_i. -/
theorem hamiltonian_commutes_projector (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    hamiltonian n ε * (cuntzS n i * cuntzSdag n i) =
    (cuntzS n i * cuntzSdag n i) * hamiltonian n ε := by
  change hamiltonian n ε * P n i = P n i * hamiltonian n ε
  rw [H_mul_P n ε i, P_mul_H n ε i]

end InfoGeometry.Algebra.CuntzHamiltonianDiagonal
