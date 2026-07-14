import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Primon Hamiltonian — H^k = Σ ε_i^k P_i

With orthogonal projectors P_i = S_i Sdag_i, H = Σ ε_i P_i
satisfies H^k = Σ ε_i^k P_i for any k ≥ 0.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace CuntzPrimonHamiltonian

def P (n : ℕ) (i : Fin n) : CuntzAlg n := cuntzS n i * cuntzSdag n i
def hamiltonian (n : ℕ) (ε : Fin n → ℂ) : CuntzAlg n := ∑ i : Fin n, ε i • P n i

theorem P_idem (n : ℕ) (i : Fin n) : P n i * P n i = P n i :=
  cuntz_range_projector n i

theorem P_ortho (n : ℕ) {i j : Fin n} (hij : i ≠ j) : P n i * P n j = 0 :=
  cuntz_range_projectors_orthogonal n hij

theorem P_sum_one (n : ℕ) : (∑ i : Fin n, P n i) = 1 :=
  cuntz_ranges_sum_one n

theorem H_mul_P (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    hamiltonian n ε * P n i = ε i • P n i := by
  dsimp [hamiltonian]
  rw [Finset.sum_mul]
  have h : ∀ j, (ε j • P n j) * P n i = (if j = i then ε i • P n i else 0) := by
    intro j; by_cases hji : j = i
    · subst j; simp [P_idem n i]
    · simp [P_ortho n hji, hji]
  rw [Finset.sum_congr rfl (λ j _ => by rw [h j])]
  simp [Finset.mem_univ]

theorem P_mul_H (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    P n i * hamiltonian n ε = ε i • P n i := by
  dsimp [hamiltonian]
  rw [Finset.mul_sum]
  have h : ∀ j, P n i * (ε j • P n j) = (if j = i then ε i • P n i else 0) := by
    intro j; by_cases hji : j = i
    · subst j; simp [P_idem n i]
    · simp [P_ortho n (Ne.symm hji), hji]
  rw [Finset.sum_congr rfl (λ j _ => by rw [h j])]
  simp [Finset.mem_univ]

theorem H_pow_eq (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) :
    (hamiltonian n ε) ^ k = ∑ i : Fin n, (ε i ^ k) • P n i := by
  induction' k with k ih
  · rw [pow_zero, ← P_sum_one n]
    refine Finset.sum_congr rfl (λ i _ => ?_)
    simp [P]
  · rw [pow_succ', ih]
    -- H * (Σ ε_i^k P_i) = Σ_i (ε_i^k) · H · P_i = Σ_i ε_i^{k+1} · P_i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (λ i _ => ?_)
    rw [mul_smul_comm, H_mul_P n ε, smul_smul, pow_succ]

end CuntzPrimonHamiltonian
