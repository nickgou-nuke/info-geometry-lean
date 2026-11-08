import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
    (hamiltonian n ε) ^ k = ∑ i : Fin n, (ε i) ^ k • P n i := by
  have h_main : ∀ (k : ℕ), (hamiltonian n ε) ^ k = ∑ i : Fin n, (ε i) ^ k • P n i := by
    intro k
    induction k with
    | zero =>
      simp [hamiltonian, Finset.sum_const, Finset.card_range]
      <;>
      simp_all [P_sum_one]
    | succ k ih =>
      have hpow : (hamiltonian n ε) ^ (k + 1) = (hamiltonian n ε) ^ k * hamiltonian n ε := by
        simp [pow_succ]
      rw [hpow, ih, Finset.sum_mul]
      have h₁ : ∀ i, ((ε i) ^ k • P n i) * (hamiltonian n ε) = (ε i) ^ (k + 1) • P n i := by
        intro i
        calc
          ((ε i) ^ k • P n i) * (hamiltonian n ε) = (ε i) ^ k • (P n i * hamiltonian n ε) := by
            simp [smul_mul_assoc]
          _ = (ε i) ^ k • ((ε i) • P n i) := by
            rw [P_mul_H]
          _ = (ε i) ^ (k + 1) • P n i := by
            simp [pow_succ, smul_smul, Complex.ext_iff, Complex.I_mul_I]
      apply Finset.sum_congr rfl
      intro i _
      rw [h₁ i]
  exact h_main k

end InfoGeometry.Algebra.CuntzPrimonHamiltonian
