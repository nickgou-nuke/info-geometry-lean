/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Order
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Relational Field Archetype Poset, Gibbs Distribution, and Bistochastic Transport

This module formalizes:
1. A finite 8-element linearly ordered archetype index set with causal cones (order ideals).
2. Gibbs softmax partition function, normalization, and energy-shift gauge invariance on finite types.
3. Bistochastic matrix properties and convex combination closure in the Birkhoff polytope.
4. Discrete monotone Lyapunov potential dissipation.
5. An explicit transition step on the archetype enum.

## Mathematical Content

- **Archetype Order**: An 8-element type `StreamArchetype` equipped with a `LinearOrder`
  via `LinearOrder.lift'` on rank.
- **Causal Cones**: Lower and upper sets $\operatorname{causalPast}(a) = \{x \mid x \le a\}$
  and $\operatorname{causalFuture}(a) = \{x \mid a \le x\}$, satisfying
  $a \le b \iff \operatorname{causalPast}(a) \subseteq \operatorname{causalPast}(b)$.
- **Gibbs Softmax**: On any non-empty finite type $\iota$, the Gibbs weights
  $p_i = \exp(-\beta E_i) / \sum_j \exp(-\beta E_j)$ are positive, sum to 1, and are invariant
  under constant shift $E_i \mapsto E_i + c$.
- **Birkhoff Polytope**: The identity matrix is bistochastic, and convex combinations
  $\alpha M_1 + (1 - \alpha) M_2$ of bistochastic matrices are bistochastic.
- **Monotone Dissipation**: Sequences satisfying $V(t+1) \le V(t)$ satisfy $V(t) \le V(0)$.
-/

namespace InfoGeometry.Canonical.RelationalFieldStream

open scoped BigOperators Matrix

/-! ### I. The Causal Poset of Stream Archetypes -/

/-- The eight canonical archetypes extracted from the relational field sequence. -/
inductive StreamArchetype
  | contextDAG
  | latentCarrier
  | energyLandscape
  | gibbsPartition
  | birkhoffTransport
  | meanFieldAttractor
  | kernelVerification
  | newContextField
  deriving DecidableEq, Repr

/-- Explicit topological rank encoding causal precedence. -/
def archetypeRank : StreamArchetype → ℕ
  | .contextDAG => 0
  | .latentCarrier => 1
  | .energyLandscape => 2
  | .gibbsPartition => 3
  | .birkhoffTransport => 4
  | .meanFieldAttractor => 5
  | .kernelVerification => 6
  | .newContextField => 7

theorem archetypeRank_injective : Function.Injective archetypeRank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

instance : Fintype StreamArchetype where
  elems := {
    StreamArchetype.contextDAG,
    StreamArchetype.latentCarrier,
    StreamArchetype.energyLandscape,
    StreamArchetype.gibbsPartition,
    StreamArchetype.birkhoffTransport,
    StreamArchetype.meanFieldAttractor,
    StreamArchetype.kernelVerification,
    StreamArchetype.newContextField
  }
  complete := by
    intro x
    cases x <;> decide

instance : LinearOrder StreamArchetype :=
  LinearOrder.lift' archetypeRank archetypeRank_injective

/-- Backward causal cone (causal past / lower set) of an archetype: $\{x \mid x \le a\}$. -/
def causalPast (a : StreamArchetype) : Finset StreamArchetype :=
  Finset.univ.filter (· ≤ a)

/-- Forward causal cone (causal future / upper set) of an archetype: $\{x \mid a \le x\}$. -/
def causalFuture (a : StreamArchetype) : Finset StreamArchetype :=
  Finset.univ.filter (a ≤ ·)

@[simp] theorem mem_causalPast (a x : StreamArchetype) :
    x ∈ causalPast a ↔ x ≤ a := by
  simp [causalPast]

@[simp] theorem mem_causalFuture (a x : StreamArchetype) :
    x ∈ causalFuture a ↔ a ≤ x := by
  simp [causalFuture]

theorem causalPast_refl (a : StreamArchetype) :
    a ∈ causalPast a := by
  rw [mem_causalPast]

theorem causalPast_monotone {a b : StreamArchetype} (h : a ≤ b) :
    causalPast a ⊆ causalPast b := by
  intro x hx
  rw [mem_causalPast] at hx ⊢
  exact le_trans hx h

theorem causalFuture_antitone {a b : StreamArchetype} (h : a ≤ b) :
    causalFuture b ⊆ causalFuture a := by
  intro x hx
  rw [mem_causalFuture] at hx ⊢
  exact le_trans h hx

/-- Equivalence between order precedence and causal cone inclusion. -/
theorem causalPast_subset_iff (a b : StreamArchetype) :
    causalPast a ⊆ causalPast b ↔ a ≤ b := by
  constructor
  · intro h
    have ha : a ∈ causalPast a := causalPast_refl a
    have hb := h ha
    rwa [mem_causalPast] at hb
  · exact causalPast_monotone

/-! ### II. Energy Landscape and Gibbs Softmax Partition -/

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partition function $Z_\beta(E) = \sum_{i} \exp(-\beta E_i)$. -/
def partition (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * E i)

/-- The normalized Gibbs probability weight $p_i = \exp(-\beta E_i) / Z_\beta(E)$. -/
def gibbsWeight (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i) / partition E β

omit [DecidableEq ι] in
/-- The partition function is strictly positive for any non-empty configuration space. -/
theorem partition_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    0 < partition E β := by
  unfold partition
  exact Finset.sum_pos' (fun i _ => (Real.exp_pos _).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩

omit [DecidableEq ι] in
/-- Gibbs occupation weights are non-negative. -/
theorem gibbsWeight_nonneg [Nonempty ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ gibbsWeight E β i := by
  unfold gibbsWeight
  exact div_nonneg (Real.exp_pos _).le (partition_pos E β).le

omit [DecidableEq ι] in
/-- Gibbs occupation weights sum to exactly one. -/
theorem gibbsWeight_sum_one [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    ∑ i, gibbsWeight E β i = 1 := by
  unfold gibbsWeight partition
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos E β))

omit [DecidableEq ι] in
/-- **Energy Shift Invariance (Gauge Freedom)**:
    Shifting the energy vector uniformly by a constant $c$, $E_i \mapsto E_i + c$,
    leaves the Gibbs occupation weights identically invariant. -/
theorem gibbsWeight_shift_invariant [Nonempty ι] (E : ι → ℝ) (β c : ℝ) (i : ι) :
    gibbsWeight (fun j => E j + c) β i = gibbsWeight E β i := by
  unfold gibbsWeight partition
  have h_exp : ∀ j, Real.exp (-β * (E j + c)) = Real.exp (-β * E j) * Real.exp (-β * c) := by
    intro j
    have : -β * (E j + c) = -β * E j + -β * c := by ring
    rw [this, Real.exp_add]
  simp_rw [h_exp]
  have h_sum : (∑ j, Real.exp (-β * E j) * Real.exp (-β * c)) =
               (∑ j, Real.exp (-β * E j)) * Real.exp (-β * c) := by
    rw [Finset.sum_mul]
  rw [h_sum]
  exact mul_div_mul_right (Real.exp (-β * E i)) (∑ j, Real.exp (-β * E j))
    (ne_of_gt (Real.exp_pos (-β * c)))

end

/-! ### III. Birkhoff Polytope and Convex Stochastic Transport -/

variable {n : ℕ}

/-- A square matrix is bistochastic if all entries are non-negative,
    every row sums to 1, and every column sums to 1. -/
def IsBistochastic (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧
  (∀ i, ∑ j, M i j = 1) ∧
  (∀ j, ∑ i, M i j = 1)

/-- The identity matrix is bistochastic. -/
theorem one_is_bistochastic :
    IsBistochastic (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    dsimp [Matrix.one_apply]
    split_ifs <;> linarith
  · intro i
    dsimp [Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hne
      simp [hne.symm]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · intro j
    dsimp [Matrix.one_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hne
      simp [hne]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))

/-- **Convex Closure of Birkhoff Polytope**:
    A convex combination $\alpha M_1 + (1 - \alpha) M_2$ of bistochastic matrices
    is itself bistochastic. -/
theorem convex_combination_bistochastic
    (M1 M2 : Matrix (Fin n) (Fin n) ℝ)
    (h1 : IsBistochastic M1) (h2 : IsBistochastic M2)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsBistochastic (α • M1 + (1 - α) • M2) := by
  have h1_sub_α : 0 ≤ 1 - α := by linarith
  rcases h1 with ⟨h1_nonneg, h1_row, h1_col⟩
  rcases h2 with ⟨h2_nonneg, h2_row, h2_col⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    dsimp [Matrix.add_apply, Matrix.smul_apply]
    have p1 : 0 ≤ α * M1 i j := mul_nonneg hα0 (h1_nonneg i j)
    have p2 : 0 ≤ (1 - α) * M2 i j := mul_nonneg h1_sub_α (h2_nonneg i j)
    linarith
  · intro i
    dsimp [Matrix.add_apply, Matrix.smul_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h1_row i, h2_row i]
    linarith
  · intro j
    dsimp [Matrix.add_apply, Matrix.smul_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h1_col j, h2_col j]
    linarith

/-! ### IV. Discrete Monotone Potential Dissipation -/

/-- A discrete sequence is decreasing if $V(t+1) \le V(t)$ for all $t$. -/
def IsDecreasingSeq (V : ℕ → ℝ) : Prop :=
  ∀ t, V (t + 1) ≤ V t

/-- Every state on a decreasing sequence is bounded by the initial value $V(0)$. -/
theorem decreasing_seq_bounded_by_initial (V : ℕ → ℝ) (hV : IsDecreasingSeq V) (t : ℕ) :
    V t ≤ V 0 := by
  induction' t with t ih
  · exact le_rfl
  · exact le_trans (hV t) ih

/-! ### V. Archetype Transition Step -/

/-- An explicit transition function advancing from `.kernelVerification` to `.newContextField`. -/
def archetypeAdvance : StreamArchetype → StreamArchetype
  | .kernelVerification => .newContextField
  | a => a

/-- Definitional readback: advancing on `.kernelVerification` yields `.newContextField`. -/
theorem archetypeAdvance_eval :
    archetypeAdvance .kernelVerification = .newContextField :=
  rfl

/-- Every archetype except `.newContextField` causally precedes `.kernelVerification`. -/
theorem kernelVerification_causal_precedence (a : StreamArchetype)
    (ha : a ≠ .newContextField) :
    a ≤ .kernelVerification := by
  change archetypeRank a ≤ archetypeRank .kernelVerification
  cases a <;> first | decide | contradiction

end InfoGeometry.Canonical.RelationalFieldStream
