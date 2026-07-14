import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Primon Hamiltonian — H^k = Σ ε_i^k P_i

With orthogonal projectors P_i = S_i Sdag_i, H = Σ ε_i P_i
satisfies H^k = Σ ε_i^k P_i for any k ≥ 0.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzPrimonHamiltonian

def P (n : ℕ) (i : Fin n) : CuntzAlg n := cuntzS n i * cuntzSdag n i
def hamiltonian (n : ℕ) (ε : Fin n → ℂ) : CuntzAlg n := ∑ i : Fin n, ε i • P n i

theorem P_idem (n : ℕ) (i : Fin n) : P n i * P n i = P n i :=
  cuntz_range_projector n i

theorem P_ortho (n : ℕ) {i j : Fin n} (hij : i ≠ j) : P n i * P n j = 0 :=
  cuntz_range_projectors_orthogonal n hij

theorem P_sum_one (n : ℕ) : (∑ i : Fin n, P n i) = 1 :=
  cuntz_ranges_sum_one n

lemma smul_P_mul_P (n : ℕ) (ε : Fin n → ℂ) (i j : Fin n) :
    (ε j • P n j) * P n i = (if j = i then ε i • P n i else 0) := by
  by_cases hji : j = i
  · subst j; simp [P_idem n i]
  · simp [P_ortho n hji, hji]

theorem H_mul_P (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    hamiltonian n ε * P n i = ε i • P n i := by
  dsimp [hamiltonian]
  rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (λ j _ => smul_P_mul_P n ε i j)]
  simp [Finset.mem_univ]

lemma P_mul_smul_P (n : ℕ) (ε : Fin n → ℂ) (i j : Fin n) :
    P n i * (ε j • P n j) = (if j = i then ε i • P n i else 0) := by
  by_cases hji : j = i
  · subst j; simp [P_idem n i]
  · simp [P_ortho n (Ne.symm hji), hji]

theorem P_mul_H (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    P n i * hamiltonian n ε = ε i • P n i := by
  dsimp [hamiltonian]
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (λ j _ => P_mul_smul_P n ε i j)]
  simp [Finset.mem_univ]

lemma H_pow_zero_eq (n : ℕ) (ε : Fin n → ℂ) :
    (hamiltonian n ε) ^ 0 = ∑ i : Fin n, (ε i ^ 0) • P n i := by
  rw [pow_zero, ← P_sum_one n]
  refine Finset.sum_congr rfl (λ i _ => ?_)
  simp [P]

lemma H_pow_succ_step (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) (i : Fin n) :
    hamiltonian n ε * ((ε i ^ k) • P n i) = (ε i ^ (k + 1)) • P n i := by
  rw [mul_smul_comm, H_mul_P n ε, smul_smul, pow_succ]

theorem H_pow_eq (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) :
    (hamiltonian n ε) ^ k = ∑ i : Fin n, (ε i ^ k) • P n i := by
  induction' k with k ih
  · exact H_pow_zero_eq n ε
  · rw [pow_succ', ih, Finset.mul_sum]
    exact Finset.sum_congr rfl (λ i _ => H_pow_succ_step n ε k i)

end InfoGeometry.Algebra.CuntzPrimonHamiltonian
