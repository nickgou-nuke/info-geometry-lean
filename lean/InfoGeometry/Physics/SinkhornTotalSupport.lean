/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornSupportConvergence
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Total support and square Sinkhorn scaling

For square nonnegative kernels with unit marginals, support-faithful feasibility
is equivalent to an explicit permutation support condition. A supported
permutation exists and every positive entry lies on one. Averaging all supported
permutations constructs a feasible coupling; the converse uses native Mathlib's
Birkhoff decomposition. The resulting convergence theorem has no supplied
feasible coupling or supplied balancing factors.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Total support includes existence of a positive permutation and coverage of
all positive entries by positive permutations. The existence clause excludes
an entirely zero nonempty kernel. -/
def HasTotalSupport (K : TransportPlan N N) : Prop :=
  (∃ σ : Equiv.Perm N, ∀ i, 0 < K i (σ i)) ∧
    ∀ i j, 0 < K i j → ∃ σ : Equiv.Perm N,
      σ i = j ∧ ∀ k, 0 < K k (σ k)

abbrev SupportedPermutation (K : TransportPlan N N) :=
  {σ : Equiv.Perm N // ∀ i, 0 < K i (σ i)}
local instance supportedPermutationFintype (K : TransportPlan N N) :
    Fintype (SupportedPermutation K) := Fintype.ofFinite _

/-- Averaging all supported permutations constructs the relative-interior
feasible coupling, so the hypothesis is combinatorial rather than variational. -/
theorem exists_support_feasible_of_totalSupport (K : TransportPlan N N)
    (hK : ∀ i j, 0 ≤ K i j) (hT : HasTotalSupport K) :
    ∃ P : TransportPlan N N, P ∈ doublyStochastic ℝ N ∧
      ∀ i j, P i j = 0 ↔ K i j = 0 := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hT.1
  letI : Nonempty (SupportedPermutation K) := ⟨⟨σ₀, hσ₀⟩⟩
  have hcard : (0 : ℝ) < Fintype.card (SupportedPermutation K) := by
    exact_mod_cast (Fintype.card_pos (α := SupportedPermutation K))
  let P : TransportPlan N N := fun i j =>
    (∑ σ : SupportedPermutation K, σ.1.permMatrix ℝ i j) /
      Fintype.card (SupportedPermutation K)
  have hperm (σ : SupportedPermutation K) : σ.1.permMatrix ℝ ∈ doublyStochastic ℝ N :=
    permMatrix_mem_doublyStochastic
  have hP : ∀ i j, 0 ≤ P i j := by
    intro i j
    exact div_nonneg (Finset.sum_nonneg fun σ _ => (hperm σ).1 i j) hcard.le
  have hrow : ∀ i, rowMass P i = 1 := by
    intro i
    change (∑ j, (∑ σ : SupportedPermutation K, σ.1.permMatrix ℝ i j) /
      (Fintype.card (SupportedPermutation K) : ℝ)) = 1
    rw [← Finset.sum_div, Finset.sum_comm]
    have hs (σ : SupportedPermutation K) : ∑ j, σ.1.permMatrix ℝ i j = 1 :=
      sum_row_of_mem_doublyStochastic (hperm σ) i
    simp_rw [hs]
    simp [hcard.ne']
  have hcol : ∀ j, colMass P j = 1 := by
    intro j
    change (∑ i, (∑ σ : SupportedPermutation K, σ.1.permMatrix ℝ i j) /
      (Fintype.card (SupportedPermutation K) : ℝ)) = 1
    rw [← Finset.sum_div, Finset.sum_comm]
    have hs (σ : SupportedPermutation K) : ∑ i, σ.1.permMatrix ℝ i j = 1 :=
      sum_col_of_mem_doublyStochastic (hperm σ) j
    simp_rw [hs]
    simp [hcard.ne']
  refine ⟨P, mem_doublyStochastic_iff_sum.2 ⟨hP, hrow, hcol⟩, ?_⟩
  have hzero (i j : N) (hz : K i j = 0) : P i j = 0 := by
    have hterms (σ : SupportedPermutation K) : σ.1.permMatrix ℝ i j = 0 := by
      have hne : σ.1 i ≠ j := by
        intro he
        have hp := σ.2 i
        rw [he, hz] at hp
        exact lt_irrefl 0 hp
      simp [Equiv.toPEquiv_apply, hne]
    have hzsum : (∑ σ : SupportedPermutation K, σ.1.permMatrix ℝ i j) = 0 :=
      Finset.sum_eq_zero fun σ _ => hterms σ
    change (∑ σ : SupportedPermutation K, σ.1.permMatrix ℝ i j) /
      (Fintype.card (SupportedPermutation K) : ℝ) = 0
    rw [hzsum, zero_div]
  have hpos (i j : N) (hp : 0 < K i j) : 0 < P i j := by
    obtain ⟨σ, hσij, hσ⟩ := hT.2 i j hp
    apply div_pos ?_ hcard
    apply Finset.sum_pos' (fun τ _ => (hperm τ).1 i j)
    refine ⟨⟨σ, hσ⟩, Finset.mem_univ _, ?_⟩
    simp [Equiv.toPEquiv_apply, hσij]
  intro i j
  constructor
  · intro hz
    by_contra hn
    exact (hpos i j (lt_of_le_of_ne (hK i j) (Ne.symm hn))).ne' hz
  · exact hzero i j

/-- Birkhoff decomposition supplies a supported positive permutation through
each positive entry of a support-faithful doubly stochastic coupling. -/
theorem totalSupport_of_support_feasible (K P : TransportPlan N N)
    (hK : ∀ i j, 0 ≤ K i j) (hP : P ∈ doublyStochastic ℝ N)
    (hPK : ∀ i j, P i j = 0 ↔ K i j = 0) : HasTotalSupport K := by
  obtain ⟨w, hw, hsum, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hentry (i j : N) :
      (∑ σ : Equiv.Perm N, w σ * σ.permMatrix ℝ i j) = P i j := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      congrFun (congrFun he i) j
  have hterms (i j : N) (σ : Equiv.Perm N) :
      0 ≤ w σ * σ.permMatrix ℝ i j :=
    mul_nonneg (hw σ) (nonneg_of_mem_doublyStochastic permMatrix_mem_doublyStochastic)
  have hsupp (σ : Equiv.Perm N) (hσ : 0 < w σ) : ∀ i, 0 < K i (σ i) := by
    intro i
    have hle : w σ ≤ P i (σ i) := by
      rw [← hentry i (σ i)]
      have h := Finset.single_le_sum (fun τ _ => hterms i (σ i) τ) (Finset.mem_univ σ)
      simpa [Equiv.toPEquiv_apply] using h
    apply lt_of_le_of_ne (hK i (σ i))
    intro hz
    exact (hσ.trans_le hle).ne' ((hPK i (σ i)).2 hz.symm)
  have hwpos : 0 < ∑ σ, w σ := by rw [hsum]; exact zero_lt_one
  obtain ⟨σ, _, hσ⟩ := (Finset.sum_pos_iff_of_nonneg (fun σ _ => hw σ)).1 hwpos
  refine ⟨⟨σ, hsupp σ hσ⟩, ?_⟩
  intro i j hKij
  have hPij : 0 < P i j := lt_of_le_of_ne (hP.1 i j)
    (fun hz => hKij.ne' ((hPK i j).1 hz.symm))
  rw [← hentry i j] at hPij
  obtain ⟨τ, _, hτ⟩ := (Finset.sum_pos_iff_of_nonneg (fun τ _ => hterms i j τ)).1 hPij
  have hτij : τ i = j := by
    by_contra hn
    simpa [Equiv.toPEquiv_apply, hn] using hτ
  have hwτ : 0 < w τ := by simpa [Equiv.toPEquiv_apply, hτij] using hτ
  exact ⟨τ, hτij, hsupp τ hwτ⟩

/-- Exact square unit-marginal classification by total support. -/
theorem totalSupport_iff_support_feasible (K : TransportPlan N N)
    (hK : ∀ i j, 0 ≤ K i j) :
    HasTotalSupport K ↔ ∃ P : TransportPlan N N,
      P ∈ doublyStochastic ℝ N ∧ ∀ i j, P i j = 0 ↔ K i j = 0 := by
  constructor
  · exact exists_support_feasible_of_totalSupport K hK
  · rintro ⟨P, hP, hs⟩
    exact totalSupport_of_support_feasible K P hK hP hs

/-- Total support is exactly the condition for a positive diagonal scaling to
unit marginals. No irreducibility assumption is needed for matrix uniqueness. -/
theorem totalSupport_iff_positive_balanced_scaling (K : TransportPlan N N)
    (hK : ∀ i j, 0 ≤ K i j) :
    HasTotalSupport K ↔ ∃ u v : N → ℝ,
      (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, rowMass (fun i j => u i * K i j * v j) i = 1) ∧
      (∀ j, colMass (fun i j => u i * K i j * v j) j = 1) := by
  constructor
  · intro hT
    obtain ⟨P, hP, hs⟩ := exists_support_feasible_of_totalSupport K hK hT
    have hp := mem_doublyStochastic_iff_sum.1 hP
    obtain ⟨u, v, hu, hv, hr, hc, _⟩ := exists_sinkhorn_limit_of_support_feasible K P
      (fun _ => 1) (fun _ => 1) hK (fun _ => zero_lt_one) (fun _ => zero_lt_one)
      hp.1 hs hp.2.1 hp.2.2
    exact ⟨u, v, hu, hv, hr, hc⟩
  · rintro ⟨u, v, hu, hv, hr, hc⟩
    apply totalSupport_of_support_feasible K (fun i j => u i * K i j * v j) hK
    · exact mem_doublyStochastic_iff_sum.2
        ⟨fun i j => mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le, hr, hc⟩
    · intro i j
      simp [(hu i).ne', (hv j).ne']

/-- Actual square Sinkhorn convergence and the unique supported KL projection
under the proved total-support condition. -/
theorem exists_sinkhorn_KL_projection_of_totalSupport (K : TransportPlan N N)
    (hK : ∀ i j, 0 ≤ K i j) (hT : HasTotalSupport K) :
    ∃ Q : TransportPlan N N,
      Q ∈ doublyStochastic ℝ N ∧ (∀ i j, Q i j = 0 ↔ K i j = 0) ∧
      Tendsto (sinkhornIterates K (fun _ => 1) (fun _ => 1)) atTop (𝓝 Q) ∧
      (∀ P : TransportPlan N N, P ∈ doublyStochastic ℝ N →
        (∀ i j, K i j = 0 → P i j = 0) →
        matrixKL P K = matrixKL P Q + matrixKL Q K ∧
        matrixKL Q K ≤ matrixKL P K ∧ (matrixKL P K = matrixKL Q K ↔ P = Q)) := by
  obtain ⟨P₀, hP₀, hs⟩ := exists_support_feasible_of_totalSupport K hK hT
  have hp₀ := mem_doublyStochastic_iff_sum.1 hP₀
  obtain ⟨Q, hQ, hQK, hr, hc, ht, hmin⟩ :=
    exists_sinkhorn_KL_projection_of_support_feasible K P₀ (fun _ => 1) (fun _ => 1)
      hK (fun _ => zero_lt_one) (fun _ => zero_lt_one) hp₀.1 hs hp₀.2.1 hp₀.2.2
  refine ⟨Q, mem_doublyStochastic_iff_sum.2 ⟨hQ, hr, hc⟩, hQK, ht, ?_⟩
  intro P hP hPK
  have hp := mem_doublyStochastic_iff_sum.1 hP
  exact hmin P hp.1 hPK hp.2.1 hp.2.2

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
