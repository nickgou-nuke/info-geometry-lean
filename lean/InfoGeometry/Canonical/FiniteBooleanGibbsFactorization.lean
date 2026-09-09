import Mathlib

/-! Exact finite factorization of the Boolean-occupation Gibbs sum. -/

noncomputable section

namespace InfoGeometry.Canonical

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

end InfoGeometry.Canonical
