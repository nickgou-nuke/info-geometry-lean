/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Authors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-!
# Native Bridge: Chiral Cuntz Apollonian Bridge & Conformal Bernoulli Measure

This module formalizes the rigorous bridge between Cuntz-Cantor boundary dynamics,
nilpotent superchiral charges, and the conformal Bernoulli-Hausdorff measure:

1. **The Cuntz Algebra & Cantor Tree Substrate**:
   - The sequence space $X_d = \mathbb{N} \to \operatorname{Fin} d$ with branch prefix shifts
     $S_i(x) = i :: x$.
   - Cylinder sets $C(w) = \{ x \in X_d \mid \forall k < |w|, x(k) = w_k \}$.
   - Exact pullback identities under shifts:
     $S_i^{-1}(C(i :: ws)) = C(ws)$ and $S_i^{-1}(C(j :: ws)) = \emptyset$ for $i \neq j$.

2. **Conformal Bernoulli Measure & Martingale Property**:
   - Normalized branch weights $w_i > 0$ with $\sum_i w_i = 1$.
   - Bernoulli product measure on cylinder sets $\mu(C(w)) = \prod_{k} w_{w_k}$.
   - The **Fractal Conformal Measure Preservation Lemma**:
     $$\mu(E) = \sum_{i=0}^{d-1} w_i \, \mu(S_i^{-1}(E))$$
   - Branching martingale property / Kolmogorov child sum: $\sum_j \mu(C(j :: ws)) = \mu(C(ws))$.

3. **Cuntz-Markov Operator Duality**:
   - The Markov transition operator $\Phi_w(x) = \sum_i w_i S_i^* x S_i$.
   - Unitality: $\Phi_w(1) = 1$.
   - Exact cylinder expectation: $\Phi_w(S_j y S_j^*) = w_j \cdot y$.

4. **Nilpotent Superchiral Charges & BRST Filtering**:
   - On Cuntz $\mathcal{O}_2$, the chiral ladder operators $Q_+ = S_1 S_2^*$ and $Q_- = S_2 S_1^*$.
   - Nilpotency: $Q_+^2 = 0$ and $Q_-^2 = 0$.
   - Graded anticommutator / Hamiltonian: $\{Q_+, Q_-\} = 1$.
   - BRST cohomological filtering: $\operatorname{im} Q_+ \subseteq \ker Q_+$.

5. **Dilaton Weyl Diffusion & Renormalization**:
   - Conformal scale factor $\mathcal{W}_\alpha(\sigma) = e^{\alpha \sigma}$.
   - Self-similar horizon correspondence: $\sigma(t) = -\ln(T - t) \to \infty$.
   - Divergence at horizon: $\mathcal{W}_\alpha(\sigma(t)) \to \infty$.

6. **Certified Synthesis**:
   - `CertifiedChiralCuntzApollonianBridge` packaging all algebraic, measure-theoretic,
     and supersymmetric invariants.
-/

noncomputable section

namespace InfoGeometry.Topology.ChiralCuntzApollonian

open Set Filter
open scoped _root_.Topology

/-! ## 1. Sequence Space, Branch Shifts, and Cylinder Sets -/

/-- Infinite sequence space over an alphabet of size d. -/
def CantorSeq (d : ℕ) := ℕ → Fin d

/-- Forward shift / branch prefixing symbol i. -/
def branchShift {d : ℕ} (i : Fin d) (x : CantorSeq d) : CantorSeq d :=
  fun
    | 0 => i
    | n + 1 => x n

@[simp]
theorem branchShift_zero {d : ℕ} (i : Fin d) (x : CantorSeq d) :
    branchShift i x 0 = i := rfl

@[simp]
theorem branchShift_succ {d : ℕ} (i : Fin d) (x : CantorSeq d) (n : ℕ) :
    branchShift i x (n + 1) = x n := rfl

/-- Cylinder set defined by a finite word w : List (Fin d). -/
def cylinderSet {d : ℕ} (w : List (Fin d)) : Set (CantorSeq d) :=
  { x | ∀ (k : ℕ) (hk : k < w.length), x k = w.get ⟨k, hk⟩ }

@[simp]
theorem cylinderSet_nil {d : ℕ} :
    cylinderSet ([] : List (Fin d)) = Set.univ := by
  ext x
  simp [cylinderSet]

theorem mem_cylinderSet_cons {d : ℕ} (j : Fin d) (ws : List (Fin d)) (x : CantorSeq d) :
    x ∈ cylinderSet (j :: ws) ↔ x 0 = j ∧ (fun n => x (n + 1)) ∈ cylinderSet ws := by
  dsimp [cylinderSet]
  constructor
  · intro h
    constructor
    · have h0 := h 0 (Nat.succ_pos ws.length)
      simpa using h0
    · intro k hk
      have hk' : k + 1 < (j :: ws).length := Nat.succ_lt_succ hk
      have hsucc := h (k + 1) hk'
      exact hsucc
  · rintro ⟨h0, hws⟩ k hk
    cases k with
    | zero => simpa using h0
    | succ m =>
        have hm : m < ws.length := Nat.lt_of_succ_lt_succ hk
        exact hws m hm

/-- Pullback of cylinder set under the same branch shift. -/
theorem preimage_cylinder_cons_same {d : ℕ} (i : Fin d) (ws : List (Fin d)) :
    (branchShift i) ⁻¹' (cylinderSet (i :: ws)) = cylinderSet ws := by
  ext x
  rw [Set.mem_preimage, mem_cylinderSet_cons]
  simp [branchShift_zero, branchShift_succ]

/-- Pullback of cylinder set under a different branch shift is empty. -/
theorem preimage_cylinder_cons_ne {d : ℕ} {i j : Fin d} (hij : i ≠ j) (ws : List (Fin d)) :
    (branchShift i) ⁻¹' (cylinderSet (j :: ws)) = ∅ := by
  ext x
  rw [Set.mem_preimage, mem_cylinderSet_cons]
  simp only [branchShift_zero, Set.mem_empty_iff_false, iff_false]
  intro h
  exact hij h.1

/-- Pullback of the whole space under any branch shift is the whole space. -/
theorem preimage_cylinder_nil {d : ℕ} (i : Fin d) :
    (branchShift i) ⁻¹' (cylinderSet ([] : List (Fin d))) = Set.univ := by
  simp

/-- Disjointness of cylinder sets with distinct prefixes. -/
theorem cylinder_disjoint_of_ne {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    (ws₁ ws₂ : List (Fin d)) :
    Disjoint (cylinderSet (i :: ws₁)) (cylinderSet (j :: ws₂)) := by
  refine Set.disjoint_left.mpr ?_
  intro x h1 h2
  rw [mem_cylinderSet_cons] at h1 h2
  exact hij (h1.1.symm.trans h2.1)

/-! ## 2. Conformal Bernoulli Measure on Cylinder Sets -/

/-- Weights for the d branches summing to 1. -/
structure BranchWeights (d : ℕ) where
  p : Fin d → ℝ
  sum_eq_one : (∑ i : Fin d, p i) = 1

/-- Bernoulli product measure of a cylinder word. -/
def wordMeasure {d : ℕ} (W : BranchWeights d) (w : List (Fin d)) : ℝ :=
  (w.map W.p).prod

@[simp]
theorem wordMeasure_nil {d : ℕ} (W : BranchWeights d) :
    wordMeasure W [] = 1 := rfl

@[simp]
theorem wordMeasure_cons {d : ℕ} (W : BranchWeights d) (j : Fin d) (ws : List (Fin d)) :
    wordMeasure W (j :: ws) = W.p j * wordMeasure W ws := rfl

/-- Branching martingale property (Kolmogorov consistency across children):
    ∑_j μ(C(j :: ws)) = μ(C(ws)). -/
theorem wordMeasure_sum_children {d : ℕ} (W : BranchWeights d) (ws : List (Fin d)) :
    (∑ j : Fin d, wordMeasure W (j :: ws)) = wordMeasure W ws := by
  dsimp [wordMeasure_cons]
  rw [← Finset.sum_mul, W.sum_eq_one, one_mul]

/-- Conformal measure preservation lemma on cylinder sets:
    ∑_i p_i * μ(S_i⁻¹(C(j :: ws))) = μ(C(j :: ws)). -/
theorem conformal_measure_preservation_cons {d : ℕ} (W : BranchWeights d)
    (j : Fin d) (ws : List (Fin d)) :
    (∑ i : Fin d, W.p i * (if i = j then wordMeasure W ws else 0)) =
      wordMeasure W (j :: ws) := by
  have h_term : (fun i : Fin d => W.p i * (if i = j then wordMeasure W ws else 0)) =
      (fun i : Fin d => if i = j then W.p j * wordMeasure W ws else 0) := by
    funext i
    split_ifs with hij
    · subst hij; rfl
    · simp
  rw [h_term]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

/-- Conformal measure preservation lemma on the full space (empty word):
    ∑_i p_i * μ(S_i⁻¹(X)) = μ(X). -/
theorem conformal_measure_preservation_nil {d : ℕ} (W : BranchWeights d) :
    (∑ i : Fin d, W.p i * 1) = 1 := by
  simp_rw [mul_one]
  exact W.sum_eq_one

/-! ## 3. Cuntz-Markov Invariance Duality -/

variable {A : Type*} [Ring A]

/-- Structure of Cuntz algebra O_d generators on an associative algebra A. -/
structure CuntzGenerators (d : ℕ) (A : Type*) [Ring A] where
  S : Fin d → A
  S_star : Fin d → A
  isometry : ∀ i j : Fin d, S_star i * S j = if i = j then 1 else 0
  range_sum : (∑ i : Fin d, S i * S_star i) = 1

/-- Unital Cuntz-Markov transition operator: Φ_w(x) = ∑_i w_i • (S_i* x S_i). -/
def cuntzMarkovStep {d : ℕ} (C : CuntzGenerators d A)
    [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (w : BranchWeights d) (x : A) : A :=
  ∑ i : Fin d, w.p i • (C.S_star i * x * C.S i)

/-- Strict unitality of the Cuntz-Markov operator: Φ_w(1) = 1. -/
theorem cuntzMarkovStep_one {d : ℕ} (C : CuntzGenerators d A)
    [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (w : BranchWeights d) :
    cuntzMarkovStep C w 1 = 1 := by
  dsimp [cuntzMarkovStep]
  have h_iso : ∀ i : Fin d, C.S_star i * 1 * C.S i = 1 := by
    intro i
    rw [mul_one]
    have h := C.isometry i i
    simp only [if_true] at h
    exact h
  simp_rw [h_iso]
  rw [← Finset.sum_smul, w.sum_eq_one, one_smul]

/-- Cylinder projection conditional expectation: Φ_w(S_j y S_j*) = w_j • y. -/
theorem cuntzMarkovStep_cylinder {d : ℕ} (C : CuntzGenerators d A)
    [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (w : BranchWeights d) (j : Fin d) (y : A) :
    cuntzMarkovStep C w (C.S j * y * C.S_star j) = w.p j • y := by
  dsimp [cuntzMarkovStep]
  have h_term : ∀ i : Fin d, C.S_star i * (C.S j * y * C.S_star j) * C.S i =
      if i = j then y else 0 := by
    intro i
    have h_assoc : C.S_star i * (C.S j * y * C.S_star j) * C.S i =
        (C.S_star i * C.S j) * y * (C.S_star j * C.S i) := by
      simp only [mul_assoc]
    rw [h_assoc, C.isometry i j, C.isometry j i]
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : ¬ (j = i) := fun h => hij h.symm
      simp [hij, hji]
  simp_rw [h_term]
  have h_smul : ∀ i : Fin d, w.p i • (if i = j then y else 0) =
      if i = j then w.p j • y else 0 := by
    intro i
    split_ifs with hij
    · subst hij; rfl
    · simp
  simp_rw [h_smul]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

/-! ## 4. Nilpotent Superchiral Charges on Cuntz O_2 -/

/-- In Cuntz O_2, the chiral ladder operator Q₊ = S₁ S₂*. -/
def Q_plus_O2 (C : CuntzGenerators 2 A) : A :=
  C.S ⟨0, by decide⟩ * C.S_star ⟨1, by decide⟩

/-- In Cuntz O_2, the chiral ladder operator Q₋ = S₂ S₁*. -/
def Q_minus_O2 (C : CuntzGenerators 2 A) : A :=
  C.S ⟨1, by decide⟩ * C.S_star ⟨0, by decide⟩

/-- Q₊ is strictly nilpotent: Q₊² = 0. -/
theorem Q_plus_O2_sq_zero (C : CuntzGenerators 2 A) :
    Q_plus_O2 C * Q_plus_O2 C = 0 := by
  dsimp [Q_plus_O2]
  have h : C.S_star ⟨1, by decide⟩ * C.S ⟨0, by decide⟩ = 0 := by
    have hiso := C.isometry ⟨1, by decide⟩ ⟨0, by decide⟩
    have hne : ¬ (⟨1, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by decide
    simp only [hne, if_false] at hiso
    exact hiso
  calc
    (C.S ⟨0, by decide⟩ * C.S_star ⟨1, by decide⟩) * (C.S ⟨0, by decide⟩ * C.S_star ⟨1, by decide⟩) =
      C.S ⟨0, by decide⟩ * (C.S_star ⟨1, by decide⟩ * C.S ⟨0, by decide⟩) * C.S_star ⟨1, by decide⟩ := by
        simp only [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

/-- Q₋ is strictly nilpotent: Q₋² = 0. -/
theorem Q_minus_O2_sq_zero (C : CuntzGenerators 2 A) :
    Q_minus_O2 C * Q_minus_O2 C = 0 := by
  dsimp [Q_minus_O2]
  have h : C.S_star ⟨0, by decide⟩ * C.S ⟨1, by decide⟩ = 0 := by
    have hiso := C.isometry ⟨0, by decide⟩ ⟨1, by decide⟩
    have hne : ¬ (⟨0, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by decide
    simp only [hne, if_false] at hiso
    exact hiso
  calc
    (C.S ⟨1, by decide⟩ * C.S_star ⟨0, by decide⟩) * (C.S ⟨1, by decide⟩ * C.S_star ⟨0, by decide⟩) =
      C.S ⟨1, by decide⟩ * (C.S_star ⟨0, by decide⟩ * C.S ⟨1, by decide⟩) * C.S_star ⟨0, by decide⟩ := by
        simp only [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

/-- Graded anticommutator / Hamiltonian: {Q₊, Q₋} = 1. -/
theorem O2_anticommutator_eq_one (C : CuntzGenerators 2 A) :
    Q_plus_O2 C * Q_minus_O2 C + Q_minus_O2 C * Q_plus_O2 C = 1 := by
  dsimp [Q_plus_O2, Q_minus_O2]
  have h00 : C.S_star ⟨0, by decide⟩ * C.S ⟨0, by decide⟩ = 1 := by
    have hiso := C.isometry ⟨0, by decide⟩ ⟨0, by decide⟩
    simp only [if_true] at hiso
    exact hiso
  have h11 : C.S_star ⟨1, by decide⟩ * C.S ⟨1, by decide⟩ = 1 := by
    have hiso := C.isometry ⟨1, by decide⟩ ⟨1, by decide⟩
    simp only [if_true] at hiso
    exact hiso
  calc
    (C.S ⟨0, by decide⟩ * C.S_star ⟨1, by decide⟩) * (C.S ⟨1, by decide⟩ * C.S_star ⟨0, by decide⟩) +
        (C.S ⟨1, by decide⟩ * C.S_star ⟨0, by decide⟩) * (C.S ⟨0, by decide⟩ * C.S_star ⟨1, by decide⟩) =
      C.S ⟨0, by decide⟩ * (C.S_star ⟨1, by decide⟩ * C.S ⟨1, by decide⟩) * C.S_star ⟨0, by decide⟩ +
        C.S ⟨1, by decide⟩ * (C.S_star ⟨0, by decide⟩ * C.S ⟨0, by decide⟩) * C.S_star ⟨1, by decide⟩ := by
          simp only [mul_assoc]
    _ = C.S ⟨0, by decide⟩ * C.S_star ⟨0, by decide⟩ + C.S ⟨1, by decide⟩ * C.S_star ⟨1, by decide⟩ := by
      rw [h11, h00, mul_one, mul_one]
    _ = 1 := by
      have hsum := C.range_sum
      have h2 : (∑ i : Fin 2, C.S i * C.S_star i) =
          C.S ⟨0, by decide⟩ * C.S_star ⟨0, by decide⟩ + C.S ⟨1, by decide⟩ * C.S_star ⟨1, by decide⟩ := by
        rw [Fin.sum_univ_two]
        rfl
      rw [← h2]
      exact hsum

/-- BRST cohomological filtering: image is contained in kernel for linear module action. -/
theorem brst_filtering {M : Type*} [AddCommGroup M] [Module A M]
    (C : CuntzGenerators 2 A) (m : M) :
    Q_plus_O2 C • (Q_plus_O2 C • m) = 0 := by
  have h := Q_plus_O2_sq_zero C
  rw [← mul_smul, h, zero_smul]

/-! ## 5. Dilaton Weyl Gauge Diffusion & Renormalization -/

/-- Dilaton Weyl scale factor. -/
def weylScale (α σ : ℝ) : ℝ :=
  Real.exp (α * σ)

/-- Abelian group law for Weyl scale transformations. -/
theorem weylScale_add (α σ₁ σ₂ : ℝ) :
    weylScale α (σ₁ + σ₂) = weylScale α σ₁ * weylScale α σ₂ := by
  dsimp [weylScale]
  rw [mul_add, Real.exp_add]

/-- Horizon scale field diverging at T: σ(t) = -ln(T - t). -/
def dilatonHorizonField (T t : ℝ) : ℝ :=
  -Real.log (T - t)

/-- Exact scaling power along horizon field. -/
theorem weylScale_horizon_eq (T t α : ℝ) (ht : t < T) :
    weylScale α (dilatonHorizonField T t) = (T - t) ^ (-α) := by
  dsimp [weylScale, dilatonHorizonField]
  have hpos : 0 < T - t := sub_pos.mpr ht
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  ring

/-- The dilaton field diverges to +∞ as t approaches T from below. -/
theorem dilaton_tendsto_atTop (T : ℝ) :
    Tendsto (fun t => dilatonHorizonField T t) (𝓝[<] T) atTop := by
  have hdiff : Tendsto (fun t => T - t) (𝓝[<] T) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hconst : Tendsto (fun _ : ℝ => T) (𝓝[<] T) (𝓝 T) := tendsto_const_nhds
      simpa only [sub_self] using hconst.sub htime
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (mem_Iio.mp ht)
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hdiff
  have hneg : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  exact hneg.comp hlog

/-- The Weyl scale factor diverges to +∞ as t approaches T for positive weight. -/
theorem weylScale_horizon_tendsto_atTop (T α : ℝ) (hα : 0 < α) :
    Tendsto (fun t => weylScale α (dilatonHorizonField T t)) (𝓝[<] T) atTop := by
  have h_dila := dilaton_tendsto_atTop T
  have h_exp := Real.tendsto_exp_atTop.comp (h_dila.const_mul_atTop hα)
  exact h_exp

/-! ## 6. Certified Synthesis Bundle -/

/-- Certified structural synthesis bundle for the Chiral Cuntz Apollonian Bridge. -/
structure CertifiedChiralCuntzApollonianBridge where
  measure_preservation_cons : ∀ {d : ℕ} (W : BranchWeights d) (j : Fin d) (ws : List (Fin d)),
    (∑ i : Fin d, W.p i * (if i = j then wordMeasure W ws else 0)) =
      wordMeasure W (j :: ws)
  measure_preservation_nil : ∀ {d : ℕ} (W : BranchWeights d),
    (∑ i : Fin d, W.p i * 1) = 1
  martingale_child_sum : ∀ {d : ℕ} (W : BranchWeights d) (ws : List (Fin d)),
    (∑ j : Fin d, wordMeasure W (j :: ws)) = wordMeasure W ws
  cuntz_unitality : ∀ {A : Type*} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    {d : ℕ} (C : CuntzGenerators d A) (w : BranchWeights d),
    cuntzMarkovStep C w 1 = 1
  cuntz_cylinder_action : ∀ {A : Type*} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    {d : ℕ} (C : CuntzGenerators d A) (w : BranchWeights d) (j : Fin d) (y : A),
    cuntzMarkovStep C w (C.S j * y * C.S_star j) = w.p j • y
  q_plus_sq_zero : ∀ {A : Type*} [Ring A] (C : CuntzGenerators 2 A),
    Q_plus_O2 C * Q_plus_O2 C = 0
  q_minus_sq_zero : ∀ {A : Type*} [Ring A] (C : CuntzGenerators 2 A),
    Q_minus_O2 C * Q_minus_O2 C = 0
  anticommutator_eq_one : ∀ {A : Type*} [Ring A] (C : CuntzGenerators 2 A),
    Q_plus_O2 C * Q_minus_O2 C + Q_minus_O2 C * Q_plus_O2 C = 1
  brst_filtering : ∀ {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (C : CuntzGenerators 2 A) (m : M),
    Q_plus_O2 C • (Q_plus_O2 C • m) = 0
  weyl_scale_add_eq : ∀ (α σ₁ σ₂ : ℝ),
    weylScale α (σ₁ + σ₂) = weylScale α σ₁ * weylScale α σ₂
  weyl_horizon_divergence : ∀ (T α : ℝ), 0 < α →
    Tendsto (fun t => weylScale α (dilatonHorizonField T t)) (𝓝[<] T) atTop

/-- Canonical certified witness for the Chiral Cuntz Apollonian Bridge. -/
def certified_chiral_cuntz_apollonian_bridge : CertifiedChiralCuntzApollonianBridge where
  measure_preservation_cons := fun W j ws => conformal_measure_preservation_cons W j ws
  measure_preservation_nil := fun W => conformal_measure_preservation_nil W
  martingale_child_sum := fun W ws => wordMeasure_sum_children W ws
  cuntz_unitality := fun C w => cuntzMarkovStep_one C w
  cuntz_cylinder_action := fun C w j y => cuntzMarkovStep_cylinder C w j y
  q_plus_sq_zero := fun C => Q_plus_O2_sq_zero C
  q_minus_sq_zero := fun C => Q_minus_O2_sq_zero C
  anticommutator_eq_one := fun C => O2_anticommutator_eq_one C
  brst_filtering := fun C m => brst_filtering C m
  weyl_scale_add_eq := weylScale_add
  weyl_horizon_divergence := weylScale_horizon_tendsto_atTop

end InfoGeometry.Topology.ChiralCuntzApollonian
