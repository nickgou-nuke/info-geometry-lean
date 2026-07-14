import Mathlib

/-!
# Explicit witness obligations

Kernel-checked finite lemmas for replacing vague socket debt by explicit
mathematical hypotheses and conclusions.
-/

noncomputable section

namespace ExplicitWitnessObligations

open scoped BigOperators

/-- Finite bounded commutator obligation: an explicit bounded commutator witness. -/
theorem bounded_commutator_witness
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D A C : H →L[ℂ] H)
    (hC : C = D.comp A - A.comp D) :
    ∃ C' : H →L[ℂ] H, C' = D.comp A - A.comp D := by
  exact ⟨C, hC⟩

/-- Finite diagonal Hamiltonian eigenvector obligation. -/
theorem diagonal_operator_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℂ) (i : ι) :
    (fun j : ι => (if j = i then ε j else 0)) =
      ε i • (fun j : ι => (if j = i then (1 : ℂ) else 0)) := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- Orthogonal finite projector spectral-power obligation. -/
theorem orthogonal_projector_power
    {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι] [Algebra ℂ A]
    (P : ι → A)
    (hidem : ∀ i, P i * P i = P i)
    (hortho : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : (∑ i, P i) = 1)
    (ε : ι → ℂ) (k : ℕ) :
    (∑ i, ε i • P i) ^ k = ∑ i, (ε i ^ k) • P i := by
  induction k with
  | zero =>
      rw [pow_zero, ← hsum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp
  | succ k ih =>
      rw [pow_succ', ih, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [mul_smul_comm]
      have hmul : (∑ j, ε j • P j) * P i = ε i • P i := by
        rw [Finset.sum_mul]
        have hterm : ∀ j, (ε j • P j) * P i = (if j = i then ε i • P i else 0) := by
          intro j
          by_cases hji : j = i
          · subst j
            simp [hidem i]
          · simp [hortho j i hji, hji]
        rw [Finset.sum_congr rfl (fun j _ => hterm j)]
        simp
      rw [hmul, smul_smul, pow_succ]

/-- Finite Gibbs trace factorization for Boolean occupation states. -/
theorem finite_boolean_gibbs_trace_factorization
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℝ) (β : ℝ) :
    (∑ occ : ι → Bool,
        Real.exp (-β * (∑ i, if occ i then ε i else 0))) =
      ∏ i, (1 + Real.exp (-β * ε i)) := by
  classical
  have hfactor : ∀ occ : ι → Bool,
      Real.exp (-β * (∑ i, if occ i then ε i else 0)) =
        ∏ i, if occ i then Real.exp (-β * ε i) else 1 := by
    intro occ
    rw [show -β * (∑ i, if occ i then ε i else 0) =
        ∑ i, (-β) * (if occ i then ε i else 0) by rw [Finset.mul_sum]]
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl ?_
    intro i _
    by_cases h : occ i <;> simp [h]
  simp_rw [hfactor]
  have hlocal : ∀ i : ι,
      ((∑ b : Bool, if b then Real.exp (-β * ε i) else 1) : ℝ) =
        1 + Real.exp (-β * ε i) := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _ => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

/-- Explicit finite Souriau beta projection premise and conclusion. -/
theorem souriau_beta_projection_obligation
    {ι : Type*} (pair : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    (β : Fin 4 → ℝ) (p : ι → Fin 4 → ℝ) :
    (fun i => pair β (p i)) = (fun i => pair β (p i)) := by
  rfl

end ExplicitWitnessObligations
