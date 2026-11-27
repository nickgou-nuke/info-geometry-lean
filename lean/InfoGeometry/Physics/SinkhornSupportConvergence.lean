/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornSupportScaling
import InfoGeometry.Physics.SinkhornPositiveConvergence

/-!
# Structural-zero Sinkhorn under explicit support-faithful feasibility

A nonnegative feasible coupling positive exactly on the reference support is an
explicit hypothesis. Under that condition the actual alternating iteration
converges to a positive diagonal scaling, uniquely minimizing supported KL.
This owner states the feasibility hypothesis explicitly. The downstream
`SinkhornTotalSupport` owner supplies the square unit-marginal classification;
a rectangular arbitrary-marginal Hall classification is not claimed here.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

lemma feasible_support_rows (K P : TransportPlan I J) (r : I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hr : ∀ i, 0 < r i)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hPr : ∀ i, rowMass P i = r i) : ∀ i, ∃ j, 0 < K i j := by
  intro i
  by_contra! hn
  have hzero (j : J) : P i j = 0 := hPK i j (le_antisymm (hn j) (hK i j))
  have hz : rowMass P i = 0 := by simp [rowMass, hzero]
  exact (hr i).ne' ((hPr i).symm.trans hz)

lemma feasible_support_cols (K P : TransportPlan I J) (c : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hc : ∀ j, 0 < c j)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hPc : ∀ j, colMass P j = c j) : ∀ j, ∃ i, 0 < K i j := by
  intro j
  by_contra! hn
  have hzero (i : I) : P i j = 0 := hPK i j (le_antisymm (hn i) (hK i j))
  have hz : colMass P j = 0 := by simp [colMass, hzero]
  exact (hc j).ne' ((hPc j).symm.trans hz)

lemma scalarKL_le_matrixKL_supported (P M : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hM : ∀ i j, 0 ≤ M i j)
    (hs : ∀ i j, M i j = 0 → P i j = 0) (i : I) (j : J) :
    scalarKLDivergence (P i j) (M i j) ≤ matrixKL P M := by
  have hrow : scalarKLDivergence (P i j) (M i j) ≤
      ∑ k, scalarKLDivergence (P i k) (M i k) :=
    Finset.single_le_sum (fun k _ => scalarKL_nonneg_supported (hP i k) (hM i k) (hs i k))
      (Finset.mem_univ j)
  exact hrow.trans (Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun l _ =>
      scalarKL_nonneg_supported (hP k l) (hM k l) (hs k l)) (Finset.mem_univ i))

section
variable (K : TransportPlan I J) (r : I → ℝ) (c : J → ℝ)
variable (hK : ∀ i j, 0 ≤ K i j)
variable (hrows : ∀ i, ∃ j, 0 < K i j) (hcols : ∀ j, ∃ i, 0 < K i j)
variable (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
include hK hrows hcols hr hc

theorem sinkhornIterates_lower_bound_supported (P : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hPK : ∀ i j, P i j = 0 ↔ K i j = 0)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j)
    (n : ℕ) (i : I) (j : J) (hij : 0 < K i j) :
    Real.exp (Real.log (P i j) - 1 - matrixKL P K / P i j) ≤ sinkhornIterates K r c n i j := by
  have hPij : 0 < P i j := lt_of_le_of_ne (hP i j)
    (fun hz => hij.ne' ((hPK i j).1 hz.symm))
  apply exp_le_of_scalarKL_le _ _ _ hPij
    (sinkhornIterates_pos_on_support K r c hK hrows hcols hr hc n i j hij)
  have hs : ∀ i j, sinkhornIterates K r c n i j = 0 → P i j = 0 := by
    intro i j hz
    exact (hPK i j).2 ((sinkhornIterates_zero_iff K r c hK hrows hcols hr hc n i j).1 hz)
  apply (scalarKL_le_matrixKL_supported P _ hP
    (sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc n) hs i j).trans
  simpa using sinkhornIterates_KL_antitone_supported K r c hK hrows hcols hr hc P
    (fun i j h => (hPK i j).2 h) hPr hPc (Nat.zero_le n)

theorem sinkhornIterates_upper_bound_supported (n : ℕ) (i : I) (j : J) :
    sinkhornIterates K r c (n + 1) i j ≤ c j := by
  rw [← sinkhornIterates_colMass_supported K r c hK hrows hcols hr hc n j]
  exact Finset.single_le_sum
    (fun k _ => sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc (n + 1) k j)
    (Finset.mem_univ i)

/-- Support-faithful subsequential limits have both marginals and actual factors. -/
theorem sinkhornIterates_subseq_limit_supported (P Q : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQK : ∀ i j, Q i j = 0 ↔ K i j = 0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ht : Tendsto (fun n => sinkhornIterates K r c (φ n + 1)) atTop (𝓝 Q)) :
    (∀ i, rowMass Q i = r i) ∧ (∀ j, colMass Q j = c j) ∧
      ∃ u : I → ℝ, ∃ v : J → ℝ, (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
        Q = fun i j => u i * K i j * v j := by
  have hQrow : ∀ i, 0 < rowMass Q i := by
    intro i
    obtain ⟨j, hj⟩ := hrows i
    have hQij : 0 < Q i j := lt_of_le_of_ne (hQ i j)
      (fun hz => hj.ne' ((hQK i j).1 hz.symm))
    exact Finset.sum_pos' (fun k _ => hQ i k) ⟨j, Finset.mem_univ j, hQij⟩
  let g : TransportPlan I J → ℝ := fun A => ∑ i, scalarKLDivergence (r i) (rowMass A i)
  have hgcont : ContinuousAt g Q := by
    apply tendsto_finsetSum
    intro i _
    have hsum := (continuous_rowMass (I := I) (J := J) i).continuousAt (x := Q)
    exact ((continuousAt_const.mul ((continuousAt_const.div hsum (hQrow i).ne').log
      (div_pos (hr i) (hQrow i)).ne')).sub continuousAt_const).add hsum
  have hφt : Tendsto (fun n => φ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hgap0 := (sinkhornIterates_rowGap_tendsto_supported K r c hK hrows hcols hr hc
    P hP hPK hPr hPc).comp hφt
  have hgeq (n : ℕ) : matrixKL (sinkhornRowUpdate (sinkhornIterates K r c (φ n + 1)) r)
      (sinkhornIterates K r c (φ n + 1)) = g (sinkhornIterates K r c (φ n + 1)) :=
    matrixKL_row_gap_eq_marginal _ r
      (sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc (φ n + 1)) hr
      (sinkhornIterates_rowMass_pos_supported K r c hK hrows hcols hr hc (φ n + 1))
  simp only [Function.comp_def, hgeq] at hgap0
  have hgzero : g Q = 0 := tendsto_nhds_unique (hgcont.tendsto.comp ht) hgap0
  have hqr : ∀ i, rowMass Q i = r i := by
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset I)) => scalarKLDivergence_nonneg
        (r i) (rowMass Q i) (hr i) (hQrow i))).1 hgzero
    intro i
    exact ((scalarKLDivergence_eq_zero_iff_nonneg (hr i).le (hQrow i)).1
      (hterms i (Finset.mem_univ i))).symm
  have hqc : ∀ j, colMass Q j = c j := by
    intro j
    have hlim := (continuous_colMass j).continuousAt.tendsto.comp ht
    have hconst : Tendsto (fun n => colMass (sinkhornIterates K r c (φ n + 1)) j)
        atTop (𝓝 (c j)) := by
      simp_rw [sinkhornIterates_colMass_supported K r c hK hrows hcols hr hc]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  refine ⟨hqr, hqc, scaling_of_supported_limit K Q hK hQ hQK
    (fun n => sinkhornIterates K r c (φ n + 1)) ?_ ht⟩
  intro n
  exact sinkhornIterates_scaling_supported K r c hK hrows hcols hr hc (φ n + 1)

end

/-- Structural-zero scaling and convergence, conditional exactly on a supplied
nonnegative feasible coupling with the same support as the reference kernel. -/
theorem exists_sinkhorn_limit_of_support_feasible
    (K P : TransportPlan I J) (r : I → ℝ) (c : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hP : ∀ i j, 0 ≤ P i j) (hPK : ∀ i j, P i j = 0 ↔ K i j = 0)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) :
    ∃ u : I → ℝ, ∃ v : J → ℝ,
      (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, rowMass (fun i j => u i * K i j * v j) i = r i) ∧
      (∀ j, colMass (fun i j => u i * K i j * v j) j = c j) ∧
      Tendsto (sinkhornIterates K r c) atTop (𝓝 (fun i j => u i * K i j * v j)) := by
  classical
  have hrows := feasible_support_rows K P r hK hr (fun i j h => (hPK i j).2 h) hPr
  have hcols := feasible_support_cols K P c hK hc (fun i j h => (hPK i j).2 h) hPc
  let lo : TransportPlan I J := fun i j => if 0 < K i j then
    Real.exp (Real.log (P i j) - 1 - matrixKL P K / P i j) else 0
  let hi : TransportPlan I J := fun i j => if 0 < K i j then c j else 0
  let box := Set.Icc lo hi
  have hcompact : IsCompact box := isCompact_Icc
  have hmem : ∀ n, sinkhornIterates K r c (n + 1) ∈ box := by
    intro n
    constructor
    · intro i j
      dsimp [lo]
      split_ifs with hij
      · exact sinkhornIterates_lower_bound_supported K r c hK hrows hcols hr hc
          P hP hPK hPr hPc (n + 1) i j hij
      · exact sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc (n + 1) i j
    · intro i j
      dsimp [hi]
      split_ifs with hij
      · exact sinkhornIterates_upper_bound_supported K r c hK hrows hcols hr hc n i j
      · have hz : K i j = 0 := le_antisymm (le_of_not_gt hij) (hK i j)
        exact le_of_eq ((sinkhornIterates_zero_iff K r c hK hrows hcols hr hc (n + 1) i j).2 hz)
  have hboxSupport (Q : TransportPlan I J) (hq : Q ∈ box) :
      (∀ i j, 0 ≤ Q i j) ∧ (∀ i j, Q i j = 0 ↔ K i j = 0) := by
    have hlo (i : I) (j : J) : 0 ≤ lo i j := by
      dsimp [lo]
      split_ifs <;> positivity
    refine ⟨fun i j => (hlo i j).trans (hq.1 i j), ?_⟩
    intro i j
    by_cases hij : 0 < K i j
    · have hQpos : 0 < Q i j := by
        have hl := hq.1 i j
        dsimp [lo] at hl
        rw [if_pos hij] at hl
        exact (Real.exp_pos _).trans_le hl
      simp [hQpos.ne', hij.ne']
    · have hKzero : K i j = 0 := le_antisymm (le_of_not_gt hij) (hK i j)
      have hQzero : Q i j = 0 := by
        have hh := hq.2 i j
        dsimp [hi] at hh
        rw [if_neg hij] at hh
        exact le_antisymm hh ((hlo i j).trans (hq.1 i j))
      simp [hQzero, hKzero]
  obtain ⟨Q, hQbox, φ, hφ, ht⟩ := hcompact.tendsto_subseq hmem
  have hQs := hboxSupport Q hQbox
  have hdata := sinkhornIterates_subseq_limit_supported K r c hK hrows hcols hr hc P Q
    hP (fun i j h => (hPK i j).2 h) hPr hPc hQs.1 hQs.2 φ hφ ht
  obtain ⟨u, v, hu, hv, hQe⟩ := hdata.2.2
  have hlimit : Tendsto (fun n => sinkhornIterates K r c (n + 1)) atTop (𝓝 Q) := by
    apply hcompact.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem)
    intro Q' hQ'box hcluster
    obtain ⟨ψ, hψ, ht'⟩ := hcluster.tendsto_subseq
    have hQs' := hboxSupport Q' hQ'box
    have hdata' := sinkhornIterates_subseq_limit_supported K r c hK hrows hcols hr hc P Q'
      hP (fun i j h => (hPK i j).2 h) hPr hPc hQs'.1 hQs'.2 ψ hψ ht'
    obtain ⟨u', v', hu', hv', hQ'e⟩ := hdata'.2.2
    rw [hQ'e, hQe]
    apply diagonal_scaling_unique_supported K u' u v' v hK hu' hu hv' hv
    · intro i
      rw [← hQ'e, ← hQe, hdata'.1 i, hdata.1 i]
    · intro j
      rw [← hQ'e, ← hQe, hdata'.2.1 j, hdata.2.1 j]
  refine ⟨u, v, hu, hv, ?_, ?_, ?_⟩
  · simpa only [← hQe] using hdata.1
  · simpa only [← hQe] using hdata.2.1
  · rw [← hQe]
    exact (tendsto_add_atTop_iff_nat 1).1 hlimit

/-- Exact supported KL minimizer theorem for the limit just constructed. -/
theorem exists_sinkhorn_KL_projection_of_support_feasible
    (K P₀ : TransportPlan I J) (r : I → ℝ) (c : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j) (hP₀K : ∀ i j, P₀ i j = 0 ↔ K i j = 0)
    (hP₀r : ∀ i, rowMass P₀ i = r i) (hP₀c : ∀ j, colMass P₀ j = c j) :
    ∃ Q : TransportPlan I J,
      (∀ i j, 0 ≤ Q i j) ∧ (∀ i j, Q i j = 0 ↔ K i j = 0) ∧
      (∀ i, rowMass Q i = r i) ∧ (∀ j, colMass Q j = c j) ∧
      Tendsto (sinkhornIterates K r c) atTop (𝓝 Q) ∧
      (∀ P : TransportPlan I J, (∀ i j, 0 ≤ P i j) →
        (∀ i j, K i j = 0 → P i j = 0) →
        (∀ i, rowMass P i = r i) → (∀ j, colMass P j = c j) →
        matrixKL P K = matrixKL P Q + matrixKL Q K ∧
        matrixKL Q K ≤ matrixKL P K ∧ (matrixKL P K = matrixKL Q K ↔ P = Q)) := by
  obtain ⟨u, v, hu, hv, hqr, hqc, ht⟩ := exists_sinkhorn_limit_of_support_feasible
    K P₀ r c hK hr hc hP₀ hP₀K hP₀r hP₀c
  let Q : TransportPlan I J := fun i j => u i * K i j * v j
  have hQ : ∀ i j, 0 ≤ Q i j := fun i j => mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le
  have hs : ∀ i j, Q i j = 0 ↔ K i j = 0 := by
    intro i j
    simp [Q, (hu i).ne', (hv j).ne']
  refine ⟨Q, hQ, hs, hqr, hqc, ht, ?_⟩
  intro P hP hPK hPr hPc
  have hrow : ∀ i, rowMass P i = rowMass Q i := fun i => (hPr i).trans (hqr i).symm
  have hcol : ∀ j, colMass P j = colMass Q j := fun j => (hPc j).trans (hqc j).symm
  have hid := matrixKL_pythagorean_scaling_supported P K u v hK hu hv hPK hrow hcol
  have hnon := matrixKL_nonneg_supported P Q hP hQ (fun i j h => hPK i j ((hs i j).1 h))
  have heq := matrixKL_eq_zero_iff_supported P Q hP hQ (fun i j h => hPK i j ((hs i j).1 h))
  change matrixKL P K = matrixKL P Q + matrixKL Q K at hid
  refine ⟨hid, ?_, ?_⟩
  · linarith
  · rw [hid, add_eq_right]
    exact heq

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
