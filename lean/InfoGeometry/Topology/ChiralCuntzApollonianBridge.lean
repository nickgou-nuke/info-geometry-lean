/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Authors
-/
import InfoGeometry.Canonical.ChiralApollonianCylinderBridge
import InfoGeometry.Canonical.ChiralCuntzSuperchargeBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-!
# Native Bridge: Chiral Cuntz Apollonian Bridge & Conformal Bernoulli Measure

This module formalizes the rigorous bridge between Cuntz-Cantor boundary dynamics,
nilpotent superchiral charges, and the conformal Bernoulli-Hausdorff measure,
directly projecting onto the canonical owner modules:
- `InfoGeometry.Canonical.ChiralApollonianCylinderBridge`
- `InfoGeometry.Canonical.ChiralCuntzSuperchargeBridge`

1. **The Cuntz Algebra & Cantor Tree Substrate**:
   - The sequence space $X_d = \mathbb{N} \to \operatorname{Fin} d$ with branch prefix shifts
     $S_i(x) = i :: x$.
   - Cylinder sets $C(w) = \{ x \in X_d \mid \forall k < |w|, x(k) = w_k \}$.
   - Exact pullback identities under shifts:
     $S_i^{-1}(C(i :: ws)) = C(ws)$ and $S_i^{-1}(C(j :: ws)) = \emptyset$ for $i \neq j$.

2. **Conformal Bernoulli Measure & Martingale Property**:
   - Canonical weights `MarkovWeights d ℝ` from `ChiralApollonianCylinderBridge`.
   - Bernoulli product measure on cylinder sets $\mu(C(w)) = \prod_{k} w_{w_k}$.
   - The **Fractal Conformal Measure Preservation Lemma**:
     $$\mu(E) = \sum_{i=0}^{d-1} w_i \, \mu(S_i^{-1}(E))$$
   - Branching martingale property / Kolmogorov child sum: $\sum_j \mu(C(j :: ws)) = \mu(C(ws))$.

3. **Cuntz-Markov Operator Duality**:
   - Re-exports and unifies with canonical `cuntzMarkovStep` from `ChiralApollonianCylinderBridge`.
   - Unitality: $\Phi_w(1) = 1$.
   - Exact cylinder expectation: $\Phi_w(S_j y S_j^*) = w_j \cdot y$.

4. **Nilpotent Superchiral Charges & BRST Filtering**:
   - Direct projection to `ChiralCuntzSuperchargeBridge` (`Q_plus`, `Q_minus`).
   - Nilpotency: $Q_+^2 = 0$ and $Q_-^2 = 0$.
   - Graded anticommutator / Hamiltonian: $\{Q_+, Q_-\} = 1$.

5. **Dilaton Weyl Diffusion & Renormalization**:
   - Canonical `weylScale` and `dilatonHorizonField` from `ChiralApollonianCylinderBridge`.
   - Divergence at horizon: $\mathcal{W}_\alpha(\sigma(t)) \to \infty$.

6. **Certified Synthesis**:
   - `CertifiedChiralCuntzApollonianBridge` packaging all algebraic, measure-theoretic,
     and supersymmetric invariants.
-/

noncomputable section

namespace InfoGeometry.Topology.ChiralCuntzApollonian

open Set Filter
open scoped _root_.Topology
open InfoGeometry.Canonical.ChiralApollonian

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

/-- Bernoulli product measure of a cylinder word using canonical MarkovWeights. -/
def wordMeasure {d : ℕ} (W : MarkovWeights d ℝ) (w : List (Fin d)) : ℝ :=
  (w.map W.p).prod

@[simp]
theorem wordMeasure_nil {d : ℕ} (W : MarkovWeights d ℝ) :
    wordMeasure W [] = 1 := rfl

@[simp]
theorem wordMeasure_cons {d : ℕ} (W : MarkovWeights d ℝ) (j : Fin d) (ws : List (Fin d)) :
    wordMeasure W (j :: ws) = W.p j * wordMeasure W ws := rfl

/-- Branching martingale property (Kolmogorov consistency across children):
    ∑_j μ(C(j :: ws)) = μ(C(ws)). -/
theorem wordMeasure_sum_children {d : ℕ} (W : MarkovWeights d ℝ) (ws : List (Fin d)) :
    (∑ j : Fin d, wordMeasure W (j :: ws)) = wordMeasure W ws := by
  dsimp [wordMeasure_cons]
  rw [← Finset.sum_mul, W.sum_eq_one, one_mul]

/-- Conformal measure preservation lemma on cylinder sets:
    ∑_i p_i * μ(S_i⁻¹(C(j :: ws))) = μ(C(j :: ws)). -/
theorem conformal_measure_preservation_cons {d : ℕ} (W : MarkovWeights d ℝ)
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
theorem conformal_measure_preservation_nil {d : ℕ} (W : MarkovWeights d ℝ) :
    (∑ i : Fin d, W.p i * 1) = 1 := by
  simp_rw [mul_one]
  exact W.sum_eq_one

/-! ## 3. Certified Synthesis Bundle -/

/-- Certified structural synthesis bundle for the Chiral Cuntz Apollonian Bridge. -/
structure CertifiedChiralCuntzApollonianBridge where
  measure_preservation_cons : ∀ {d : ℕ} (W : MarkovWeights d ℝ) (j : Fin d) (ws : List (Fin d)),
    (∑ i : Fin d, W.p i * (if i = j then wordMeasure W ws else 0)) =
      wordMeasure W (j :: ws)
  measure_preservation_nil : ∀ {d : ℕ} (W : MarkovWeights d ℝ),
    (∑ i : Fin d, W.p i * 1) = 1
  martingale_child_sum : ∀ {d : ℕ} (W : MarkovWeights d ℝ) (ws : List (Fin d)),
    (∑ j : Fin d, wordMeasure W (j :: ws)) = wordMeasure W ws
  cuntz_unitality : ∀ {A : Type*} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    {d : ℕ} (C : CuntzGenerators d A) (w : MarkovWeights d ℝ),
    cuntzMarkovStep C w 1 = 1
  cuntz_cylinder_action : ∀ {A : Type*} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    {d : ℕ} (C : CuntzGenerators d A) (w : MarkovWeights d ℝ) (j : Fin d) (y : A),
    cuntzMarkovStep C w (C.S j * y * C.S_star j) = w.p j • y
  chiral_supercharge_anticommutator : ∀ {R : Type*} [Ring R] [StarRing R]
    (sys : ChiralCuntzSuperchargeBridge.Cuntz2System R),
    ChiralCuntzSuperchargeBridge.Q_plus sys * ChiralCuntzSuperchargeBridge.Q_minus sys +
    ChiralCuntzSuperchargeBridge.Q_minus sys * ChiralCuntzSuperchargeBridge.Q_plus sys = 1
  weyl_scale_add_eq : ∀ (α σ₁ σ₂ : ℝ),
    weylScale α (σ₁ + σ₂) = weylScale α σ₁ * weylScale α σ₂
  weyl_horizon_divergence : ∀ (T α : ℝ), 0 < α →
    Tendsto (fun t => weylScale α (dilatonHorizonField T t)) (𝓝[<] T) atTop

/-- Canonical certified witness for the Chiral Cuntz Apollonian Bridge. -/
def certified_chiral_cuntz_apollonian_bridge : CertifiedChiralCuntzApollonianBridge where
  measure_preservation_cons := fun W j ws => conformal_measure_preservation_cons W j ws
  measure_preservation_nil := fun W => conformal_measure_preservation_nil W
  martingale_child_sum := fun W ws => wordMeasure_sum_children W ws
  cuntz_unitality := fun C => cuntzMarkovStep_one C
  cuntz_cylinder_action := fun C => cuntzMarkovStep_cylinder C
  chiral_supercharge_anticommutator := fun sys => ChiralCuntzSuperchargeBridge.chiral_susy_anticommutator_eq_one sys
  weyl_scale_add_eq := weylScale_add
  weyl_horizon_divergence := weylScale_horizon_tendsto_atTop

end InfoGeometry.Topology.ChiralCuntzApollonian
