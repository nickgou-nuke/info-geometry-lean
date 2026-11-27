/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornKLIteration
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Positive finite Sinkhorn: existence and matrix convergence

The actual alternating updates lie in a compact positive box, constructed from
KL descent against the positive product coupling. Vanishing row-step divergence
makes every cluster point balanced. Four-cycle identities reconstruct scaling
factors, and KL strictness gives a unique cluster point and whole-sequence
convergence. No balanced candidate is assumed in the existence theorem.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

/-- A positive KL reference keeps a sublevel away from zero. -/
theorem exp_le_of_scalarKL_le (x y C : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : scalarKLDivergence x y ≤ C) :
    Real.exp (Real.log x - 1 - C / x) ≤ y := by
  have hdiv : x * (C / x) = C := mul_div_cancel₀ C hx.ne'
  have hy₀ : 0 ≤ y := hy.le
  have hlog : Real.log x - 1 - C / x ≤ Real.log y := by
    apply (mul_le_mul_iff_right₀ hx).1
    rw [scalarKLDivergence, Real.log_div hx.ne' hy.ne'] at h
    nlinarith
  simpa [Real.exp_log hy] using Real.exp_le_exp.mpr hlog

theorem scalarKL_le_matrixKL (P M : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hM : ∀ i j, 0 < M i j) (i : I) (j : J) :
    scalarKLDivergence (P i j) (M i j) ≤ matrixKL P M := by
  have hrow : scalarKLDivergence (P i j) (M i j) ≤
      ∑ k, scalarKLDivergence (P i k) (M i k) :=
    Finset.single_le_sum (fun k _ => scalarKLDivergence_nonneg_left (hP i k) (hM i k))
      (Finset.mem_univ j)
  exact hrow.trans (Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun l _ =>
      scalarKLDivergence_nonneg_left (hP k l) (hM k l)) (Finset.mem_univ i))

theorem continuousAt_matrixKL {X : Type*} [TopologicalSpace X]
    {f g : X → TransportPlan I J} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hfx : ∀ i j, 0 < f x i j) (hgx : ∀ i j, 0 < g x i j) :
    ContinuousAt (fun y => matrixKL (f y) (g y)) x := by
  unfold matrixKL
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  have hfij : ContinuousAt (fun y => f y i j) x :=
    (hf.tendsto.apply_nhds i).apply_nhds j
  have hgij : ContinuousAt (fun y => g y i j) x :=
    (hg.tendsto.apply_nhds i).apply_nhds j
  exact ((hfij.mul ((hfij.div hgij (hgx i j).ne').log
    (div_pos (hfx i j) (hgx i j)).ne')).sub hfij).add hgij

theorem continuousAt_sinkhornRowUpdate [Nonempty J]
    (r : I → ℝ) (M : TransportPlan I J) (hM : ∀ i j, 0 < M i j) :
    ContinuousAt (fun Q => sinkhornRowUpdate Q r) M := by
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro j
  have hsum : (∑ k, M i k) ≠ 0 :=
    (Finset.sum_pos (fun k _ => hM i k) Finset.univ_nonempty).ne'
  exact (continuousAt_const.div (continuous_rowMass i).continuousAt hsum).mul
    (((continuous_apply j).comp (continuous_apply i)).continuousAt)

/-- An explicit feasible positive coupling, used to construct the compact sublevel. -/
def productCoupling (r : I → ℝ) (c : J → ℝ) : TransportPlan I J :=
  fun i j => r i * c j / ∑ k, r k

section Positive
variable [Nonempty I] [Nonempty J]
variable (K : TransportPlan I J) (r : I → ℝ) (c : J → ℝ)
variable (hK : ∀ i j, 0 < K i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)

include hr hc in
theorem productCoupling_pos : ∀ i j, 0 < productCoupling r c i j := by
  intro i j
  exact div_pos (mul_pos (hr i) (hc j))
    (Finset.sum_pos (fun k _ => hr k) Finset.univ_nonempty)

include hr in
theorem productCoupling_rowMass (hmass : ∑ i, r i = ∑ j, c j) (i : I) :
    rowMass (productCoupling r c) i = r i := by
  have hm : (∑ k, r k) ≠ 0 :=
    (Finset.sum_pos (fun k _ => hr k) Finset.univ_nonempty).ne'
  unfold rowMass productCoupling
  rw [← Finset.sum_div, ← Finset.mul_sum, ← hmass]
  exact mul_div_cancel_right₀ _ hm

include hr in
theorem productCoupling_colMass (j : J) :
    colMass (productCoupling r c) j = c j := by
  have hm : (∑ k, r k) ≠ 0 :=
    (Finset.sum_pos (fun k _ => hr k) Finset.univ_nonempty).ne'
  unfold colMass productCoupling
  rw [← Finset.sum_div, ← Finset.sum_mul]
  exact mul_div_cancel_left₀ _ hm

include hK hr hc

/-- Positive factors are constructed inductively at every finite iterate. -/
theorem sinkhornIterates_scaling (n : ℕ) :
    ∃ u : I → ℝ, ∃ v : J → ℝ, (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      sinkhornIterates K r c n = (fun i j => u i * K i j * v j) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => 1, fun _ => zero_lt_one, fun _ => zero_lt_one, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨u, v, hu, hv, he⟩ := ih
    let M := sinkhornIterates K r c n
    let R := sinkhornRowUpdate M r
    have hM := sinkhornIterates_pos K r c hK hr hc n
    have hR := sinkhornRowUpdate_pos M r hM hr
    let a : I → ℝ := fun i => r i / rowMass M i
    let b : J → ℝ := fun j => c j / colMass R j
    have ha : ∀ i, 0 < a i := fun i => div_pos (hr i)
      (Finset.sum_pos (fun j _ => hM i j) Finset.univ_nonempty)
    have hb : ∀ j, 0 < b j := fun j => div_pos (hc j)
      (Finset.sum_pos (fun i _ => hR i j) Finset.univ_nonempty)
    refine ⟨fun i => a i * u i, fun j => b j * v j,
      fun i => mul_pos (ha i) (hu i), fun j => mul_pos (hb j) (hv j), ?_⟩
    funext i j
    change b j * (a i * M i j) = (a i * u i) * K i j * (b j * v j)
    have hij : M i j = u i * K i j * v j := congrFun (congrFun he i) j
    rw [hij]
    ring

theorem sinkhornIterates_fourCycle (n : ℕ) (i i₀ : I) (j j₀ : J) :
    sinkhornIterates K r c n i j * sinkhornIterates K r c n i₀ j₀ *
      K i j₀ * K i₀ j =
    sinkhornIterates K r c n i j₀ * sinkhornIterates K r c n i₀ j *
      K i j * K i₀ j₀ := by
  obtain ⟨u, v, _, _, he⟩ := sinkhornIterates_scaling K r c hK hr hc n
  rw [he]
  ring

omit hr hc in
/-- Four-cycle compatibility yields explicit factors on the full positive support. -/
theorem scaling_of_fourCycle (Q : TransportPlan I J)
    (hQ : ∀ i j, 0 < Q i j)
    (hcycle : ∀ i i₀ j j₀, Q i j * Q i₀ j₀ * K i j₀ * K i₀ j =
      Q i j₀ * Q i₀ j * K i j * K i₀ j₀) :
    ∃ u : I → ℝ, ∃ v : J → ℝ, (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      Q = (fun i j => u i * K i j * v j) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨j₀⟩ := ‹Nonempty J›
  refine ⟨fun i => Q i j₀ / K i j₀,
    fun j => Q i₀ j * K i₀ j₀ / (Q i₀ j₀ * K i₀ j),
    fun i => div_pos (hQ i j₀) (hK i j₀),
    fun j => div_pos (mul_pos (hQ i₀ j) (hK i₀ j₀))
      (mul_pos (hQ i₀ j₀) (hK i₀ j)), ?_⟩
  funext i j
  have he := hcycle i i₀ j j₀
  field_simp [(hK i j₀).ne', (hQ i₀ j₀).ne', (hK i₀ j).ne']
  nlinarith [he]

theorem sinkhornIterates_uniform_lower_bound (P : TransportPlan I J)
    (hP : ∀ i j, 0 < P i j)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j)
    (n : ℕ) (i : I) (j : J) :
    Real.exp (Real.log (P i j) - 1 - matrixKL P K / P i j) ≤
      sinkhornIterates K r c n i j := by
  apply exp_le_of_scalarKL_le _ _ _ (hP i j)
    (sinkhornIterates_pos K r c hK hr hc n i j)
  apply (scalarKL_le_matrixKL P _ (fun i j => (hP i j).le)
    (sinkhornIterates_pos K r c hK hr hc n) i j).trans
  simpa using sinkhornIterates_KL_antitone K r c hK hr hc P hPr hPc (Nat.zero_le n)

theorem sinkhornIterates_upper_bound (n : ℕ) (i : I) (j : J) :
    sinkhornIterates K r c (n + 1) i j ≤ c j := by
  rw [← sinkhornIterates_colMass K r c hK hr hc n j]
  exact Finset.single_le_sum
    (fun k _ => (sinkhornIterates_pos K r c hK hr hc (n + 1) k j).le)
    (Finset.mem_univ i)

/-- Positive subsequential limits are balanced and admit constructed scaling factors. -/
theorem sinkhornIterates_subseq_limit (P Q : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j)
    (hQ : ∀ i j, 0 < Q i j)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ht : Tendsto (fun n => sinkhornIterates K r c (φ n + 1)) atTop (𝓝 Q)) :
    (∀ i, rowMass Q i = r i) ∧ (∀ j, colMass Q j = c j) ∧
      ∃ u : I → ℝ, ∃ v : J → ℝ, (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
        Q = (fun i j => u i * K i j * v j) := by
  have hφt : Tendsto (fun n => φ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hgap0 := (sinkhornIterates_rowGap_tendsto K r c hK hr hc P hP hPr hPc).comp hφt
  have hgapQ : Tendsto
      (fun n => matrixKL (sinkhornRowUpdate (sinkhornIterates K r c (φ n + 1)) r)
        (sinkhornIterates K r c (φ n + 1))) atTop
      (𝓝 (matrixKL (sinkhornRowUpdate Q r) Q)) :=
    (continuousAt_matrixKL (continuousAt_sinkhornRowUpdate r Q hQ) continuousAt_id
      (sinkhornRowUpdate_pos Q r hQ hr) hQ).tendsto.comp ht
  have hzero : matrixKL (sinkhornRowUpdate Q r) Q = 0 :=
    tendsto_nhds_unique hgapQ hgap0
  have hfix : sinkhornRowUpdate Q r = Q :=
    (matrixKL_eq_zero_iff _ Q (fun i j => (sinkhornRowUpdate_pos Q r hQ hr i j).le) hQ).1 hzero
  have hqr : ∀ i, rowMass Q i = r i := by
    intro i
    rw [← hfix]
    exact sinkhornRowUpdate_row_sum Q r i
      (Finset.sum_pos (fun j _ => hQ i j) Finset.univ_nonempty).ne'
  have hqc : ∀ j, colMass Q j = c j := by
    intro j
    have hlim := (continuous_colMass j).continuousAt.tendsto.comp ht
    have hconst : Tendsto (fun n => colMass (sinkhornIterates K r c (φ n + 1)) j)
        atTop (𝓝 (c j)) := by
      simp_rw [sinkhornIterates_colMass K r c hK hr hc]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  refine ⟨hqr, hqc, scaling_of_fourCycle K hK Q hQ ?_⟩
  intro i i₀ j j₀
  have hev (i : I) (j : J) :
      Tendsto (fun n => sinkhornIterates K r c (φ n + 1) i j) atTop (𝓝 (Q i j)) :=
    (ht.apply_nhds i).apply_nhds j
  have hleft := ((hev i j).mul (hev i₀ j₀)).mul_const (K i j₀) |>.mul_const (K i₀ j)
  have hright := ((hev i j₀).mul (hev i₀ j)).mul_const (K i j) |>.mul_const (K i₀ j₀)
  have heq : (fun n => sinkhornIterates K r c (φ n + 1) i j *
      sinkhornIterates K r c (φ n + 1) i₀ j₀ * K i j₀ * K i₀ j) =
      (fun n => sinkhornIterates K r c (φ n + 1) i j₀ *
      sinkhornIterates K r c (φ n + 1) i₀ j * K i j * K i₀ j₀) :=
    funext fun n => sinkhornIterates_fourCycle K r c hK hr hc (φ n + 1) i i₀ j j₀
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Positive finite scaling exists and the full matrix sequence converges.
The reference matrix may be rectangular; prescribed marginals have equal mass. -/
theorem exists_sinkhorn_limit (hmass : ∑ i, r i = ∑ j, c j) :
    ∃ u : I → ℝ, ∃ v : J → ℝ,
      (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, rowMass (fun i j => u i * K i j * v j) i = r i) ∧
      (∀ j, colMass (fun i j => u i * K i j * v j) j = c j) ∧
      Tendsto (sinkhornIterates K r c) atTop (𝓝 (fun i j => u i * K i j * v j)) := by
  let P := productCoupling r c
  have hP : ∀ i j, 0 < P i j := productCoupling_pos r c hr hc
  have hPr : ∀ i, rowMass P i = r i := productCoupling_rowMass r c hr hmass
  have hPc : ∀ j, colMass P j = c j := productCoupling_colMass r c hr
  let lo : TransportPlan I J := fun i j =>
    Real.exp (Real.log (P i j) - 1 - matrixKL P K / P i j)
  let hi : TransportPlan I J := fun _ j => c j
  let box := Set.Icc lo hi
  have hcompact : IsCompact box := isCompact_Icc
  have hmem : ∀ n, sinkhornIterates K r c (n + 1) ∈ box := by
    intro n
    constructor
    · intro i j
      exact sinkhornIterates_uniform_lower_bound K r c hK hr hc P hP hPr hPc (n + 1) i j
    · intro i j
      exact sinkhornIterates_upper_bound K r c hK hr hc n i j
  obtain ⟨Q, hQbox, φ, hφ, ht⟩ := hcompact.tendsto_subseq hmem
  have hQ : ∀ i j, 0 < Q i j :=
    fun i j => (Real.exp_pos _).trans_le (hQbox.1 i j)
  have hdata := sinkhornIterates_subseq_limit K r c hK hr hc P Q
    (fun i j => (hP i j).le) hPr hPc hQ φ hφ ht
  obtain ⟨u, v, hu, hv, hQe⟩ := hdata.2.2
  have hlimit : Tendsto (fun n => sinkhornIterates K r c (n + 1)) atTop (𝓝 Q) := by
    apply hcompact.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem)
    intro Q' hQ'box hcluster
    obtain ⟨ψ, hψ, ht'⟩ := hcluster.tendsto_subseq
    have hQ' : ∀ i j, 0 < Q' i j :=
      fun i j => (Real.exp_pos _).trans_le (hQ'box.1 i j)
    have hdata' := sinkhornIterates_subseq_limit K r c hK hr hc P Q'
      (fun i j => (hP i j).le) hPr hPc hQ' ψ hψ ht'
    obtain ⟨u', v', hu', hv', hQ'e⟩ := hdata'.2.2
    rw [hQ'e, hQe]
    apply diagonal_scaling_unique K u' u v' v hK hu' hu hv' hv
    · intro i
      rw [← hQ'e, ← hQe, hdata'.1 i, hdata.1 i]
    · intro j
      rw [← hQ'e, ← hQe, hdata'.2.1 j, hdata.2.1 j]
  refine ⟨u, v, hu, hv, ?_, ?_, ?_⟩
  · simpa only [← hQe] using hdata.1
  · simpa only [← hQe] using hdata.2.1
  · rw [← hQe]
    exact (tendsto_add_atTop_iff_nat 1).1 hlimit

/-- The limit is the unique constrained KL minimizer, also against zero entries. -/
theorem exists_unique_sinkhorn_KL_projection (hmass : ∑ i, r i = ∑ j, c j) :
    ∃ Q : TransportPlan I J,
      (∀ i j, 0 < Q i j) ∧
      (∀ i, rowMass Q i = r i) ∧ (∀ j, colMass Q j = c j) ∧
      Tendsto (sinkhornIterates K r c) atTop (𝓝 Q) ∧
      (∀ P : TransportPlan I J, (∀ i j, 0 ≤ P i j) →
        (∀ i, rowMass P i = r i) → (∀ j, colMass P j = c j) →
        matrixKL P K = matrixKL P Q + matrixKL Q K ∧
        matrixKL Q K ≤ matrixKL P K ∧
        (matrixKL P K = matrixKL Q K ↔ P = Q)) := by
  obtain ⟨u, v, hu, hv, hqr, hqc, ht⟩ := exists_sinkhorn_limit K r c hK hr hc hmass
  refine ⟨fun i j => u i * K i j * v j,
    fun i j => mul_pos (mul_pos (hu i) (hK i j)) (hv j), hqr, hqc, ht, ?_⟩
  intro P hP hPr hPc
  have hrow : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i :=
    fun i => (hPr i).trans (hqr i).symm
  have hcol : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j :=
    fun j => (hPc j).trans (hqc j).symm
  exact ⟨matrixKL_pythagorean_of_scaling P K u v hK hu hv hrow hcol,
    matrixKL_scaling_minimizes P K u v hP hK hu hv hrow hcol,
    matrixKL_scaling_eq_iff P K u v hP hK hu hv hrow hcol⟩

end Positive
end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
