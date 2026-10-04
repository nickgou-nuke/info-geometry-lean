
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Group
import Mathlib.Tactic

open Relation

namespace PlabicPureBraidMapping

/-! ### 1. Plabic Graph Invariants & Combinatorial Structure -/

/-- Combinatorial parameters of an on-shell plabic graph:
    - `V_black`: Number of trivalent MHV_3 vertices (k = 2)
    - `V_white`: Number of trivalent MHVbar_3 vertices (k = 1)
    - `E_internal`: Number of internal on-shell phase space propagators -/
structure PlabicCounts where
  V_black : ℤ
  V_white : ℤ
  E_internal : ℤ
  deriving Repr, DecidableEq

/-- The Grassmannian helicity degree k = 2 * V_black + V_white - E_internal. -/
def kGrassmannian (p : PlabicCounts) : ℤ :=
  2 * p.V_black + p.V_white - p.E_internal

/-- The number of external legs n_ext = 3 * (V_black + V_white) - 2 * E_internal. -/
def nExternal (p : PlabicCounts) : ℤ :=
  3 * (p.V_black + p.V_white) - 2 * p.E_internal

/-- The quantum chiral / helicity defect Δh = V_black - V_white. -/
def helicityDefect (p : PlabicCounts) : ℤ :=
  p.V_black - p.V_white

/-! ### 2. Atomic Cluster Moves and Graph Equivalence -/

/-- Square Move (Urban Renewal on an alternating 4-face). -/
def applySquareMove (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black - 2 + 2
    V_white := p.V_white - 2 + 2
    E_internal := p.E_internal - 4 + 4 }

/-- Bubble Reduction: collapse of a 2-cycle dipole. -/
def applyBubbleRed (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black - 1
    V_white := p.V_white - 1
    E_internal := p.E_internal - 3 }

/-- Bubble Creation: expansion of a 2-cycle dipole. -/
def applyBubbleCre (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black + 1
    V_white := p.V_white + 1
    E_internal := p.E_internal + 3 }

/-- Inductive step for atomic cluster moves on plabic graphs. -/
inductive AtomicClusterMove : PlabicCounts → PlabicCounts → Prop where
  | square (p : PlabicCounts) : AtomicClusterMove p (applySquareMove p)
  | bubbleRed (p : PlabicCounts) : AtomicClusterMove p (applyBubbleRed p)
  | bubbleCre (p : PlabicCounts) : AtomicClusterMove p (applyBubbleCre p)

/-- Equivalence of plabic graphs under finite sequences of cluster mutations. -/
def ClusterEquiv (p p' : PlabicCounts) : Prop :=
  ReflTransGen AtomicClusterMove p p'

/-! ### 3. Invariance of Topological Indices under Cluster Sequences -/

theorem k_invariant_of_atomic {p p' : PlabicCounts} (h : AtomicClusterMove p p') :
    kGrassmannian p' = kGrassmannian p := by
  cases h <;> { dsimp [applySquareMove, applyBubbleRed, applyBubbleCre, kGrassmannian]; ring }

theorem next_invariant_of_atomic {p p' : PlabicCounts} (h : AtomicClusterMove p p') :
    nExternal p' = nExternal p := by
  cases h <;> { dsimp [applySquareMove, applyBubbleRed, applyBubbleCre, nExternal]; ring }

theorem helicityDefect_invariant_of_atomic {p p' : PlabicCounts} (h : AtomicClusterMove p p') :
    helicityDefect p' = helicityDefect p := by
  cases h <;> { dsimp [applySquareMove, applyBubbleRed, applyBubbleCre, helicityDefect]; ring }

theorem clusterEquiv_preserves_k {p p' : PlabicCounts} (h : ClusterEquiv p p') :
    kGrassmannian p' = kGrassmannian p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [k_invariant_of_atomic hstep, ih]

theorem clusterEquiv_preserves_next {p p' : PlabicCounts} (h : ClusterEquiv p p') :
    nExternal p' = nExternal p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [next_invariant_of_atomic hstep, ih]

theorem clusterEquiv_preserves_helicityDefect {p p' : PlabicCounts} (h : ClusterEquiv p p') :
    helicityDefect p' = helicityDefect p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [helicityDefect_invariant_of_atomic hstep, ih]

/-! ### 4. Pure Braid Representation on Cluster Mutation Groups -/

structure ClusterBraidRep (G : Type*) [Group G] (n : ℕ) where
  mu : Fin n → Fin n → G
  disjoint_comm : ∀ i j k l : Fin n,
    i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l →
    mu i j * mu k l = mu k l * mu i j
  cyclic_one : ∀ i j k : Fin n,
    i < j → j < k →
    mu i j * mu i k * mu j k = mu i k * mu j k * mu i j
  cyclic_two : ∀ i j k : Fin n,
    i < j → j < k →
    mu i k * mu j k * mu i j = mu j k * mu i j * mu i k

namespace ClusterBraidRep

variable {G : Type*} [Group G] {n : ℕ} (rep : ClusterBraidRep G n)

theorem cyclic_three {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    rep.mu j k * rep.mu i j * rep.mu i k = rep.mu i j * rep.mu i k * rep.mu j k := by
  rw [rep.cyclic_one i j k hij hjk, rep.cyclic_two i j k hij hjk]

theorem comm_mu_ij_prod {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    rep.mu i j * (rep.mu i k * rep.mu j k) = (rep.mu i k * rep.mu j k) * rep.mu i j := by
  have h := rep.cyclic_one i j k hij hjk
  calc rep.mu i j * (rep.mu i k * rep.mu j k)
      = rep.mu i j * rep.mu i k * rep.mu j k := by group
    _ = rep.mu i k * rep.mu j k * rep.mu i j := h
    _ = (rep.mu i k * rep.mu j k) * rep.mu i j := by group

theorem comm_mu_ik_prod {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    rep.mu i k * (rep.mu j k * rep.mu i j) = (rep.mu j k * rep.mu i j) * rep.mu i k := by
  have h := rep.cyclic_two i j k hij hjk
  calc rep.mu i k * (rep.mu j k * rep.mu i j)
      = rep.mu i k * rep.mu j k * rep.mu i j := by group
    _ = rep.mu j k * rep.mu i j * rep.mu i k := h
    _ = (rep.mu j k * rep.mu i j) * rep.mu i k := by group

theorem artin_crossing_cluster_Y {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    rep.mu i j * rep.mu i k * (rep.mu i j)⁻¹ =
      (rep.mu j k)⁻¹ * rep.mu i k * rep.mu j k := by
  have h_comm := rep.comm_mu_ik_prod hij hjk
  calc rep.mu i j * rep.mu i k * (rep.mu i j)⁻¹
      = (rep.mu j k)⁻¹ * ((rep.mu j k * rep.mu i j) * rep.mu i k) * (rep.mu i j)⁻¹ := by group
    _ = (rep.mu j k)⁻¹ * (rep.mu i k * (rep.mu j k * rep.mu i j)) * (rep.mu i j)⁻¹ := by rw [← h_comm]
    _ = (rep.mu j k)⁻¹ * rep.mu i k * rep.mu j k := by group

theorem artin_crossing_cluster_Y_factored {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    rep.mu i j * rep.mu i k * (rep.mu i j)⁻¹ =
      (rep.mu i k * rep.mu j k)⁻¹ * rep.mu i k * (rep.mu i k * rep.mu j k) := by
  have h_group : ∀ (Y Z : G), (Y * Z)⁻¹ * Y * (Y * Z) = Z⁻¹ * Y * Z := by
    intro Y Z; group
  rw [h_group]
  exact rep.artin_crossing_cluster_Y hij hjk

theorem artin_crossing_cluster_Z {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    (rep.mu i j)⁻¹ * rep.mu j k * rep.mu i j =
      rep.mu i k * rep.mu j k * (rep.mu i k)⁻¹ := by
  have h_cyc3 := rep.cyclic_three hij hjk
  have h_comm : rep.mu j k * (rep.mu i j * rep.mu i k) =
      (rep.mu i j * rep.mu i k) * rep.mu j k := by
    calc rep.mu j k * (rep.mu i j * rep.mu i k)
        = rep.mu j k * rep.mu i j * rep.mu i k := by group
      _ = rep.mu i j * rep.mu i k * rep.mu j k := h_cyc3
      _ = (rep.mu i j * rep.mu i k) * rep.mu j k := by group
  calc (rep.mu i j)⁻¹ * rep.mu j k * rep.mu i j
      = (rep.mu i j)⁻¹ * (rep.mu j k * (rep.mu i j * rep.mu i k)) * (rep.mu i k)⁻¹ := by group
    _ = (rep.mu i j)⁻¹ * ((rep.mu i j * rep.mu i k) * rep.mu j k) * (rep.mu i k)⁻¹ := by rw [h_comm]
    _ = rep.mu i k * rep.mu j k * (rep.mu i k)⁻¹ := by group

end ClusterBraidRep

structure PlabicClusterAction (G : Type*) [Group G] where
  act : G → PlabicCounts → PlabicCounts
  act_one : ∀ p, act 1 p = p
  act_mul : ∀ g h p, act (g * h) p = act g (act h p)
  act_equiv : ∀ g p, ClusterEquiv p (act g p)

theorem crossing_plabic_action_eq {G : Type*} [Group G] {n : ℕ}
    (rep : ClusterBraidRep G n) (action : PlabicClusterAction G)
    {i j k : Fin n} (hij : i < j) (hjk : j < k) (p : PlabicCounts) :
    action.act (rep.mu i j * rep.mu i k * (rep.mu i j)⁻¹) p =
    action.act ((rep.mu j k)⁻¹ * rep.mu i k * rep.mu j k) p := by
  rw [rep.artin_crossing_cluster_Y hij hjk]

theorem pure_braid_preserves_plabic_invariants {G : Type*} [Group G]
    (action : PlabicClusterAction G) (g : G) (p : PlabicCounts) :
    kGrassmannian (action.act g p) = kGrassmannian p ∧
    nExternal (action.act g p) = nExternal p ∧
    helicityDefect (action.act g p) = helicityDefect p := by
  have h_equiv := action.act_equiv g p
  exact ⟨clusterEquiv_preserves_k h_equiv,
         clusterEquiv_preserves_next h_equiv,
         clusterEquiv_preserves_helicityDefect h_equiv⟩

theorem zamolodchikov_cluster_pentagon_period {F : Type*} [Field F]
    (x₀ x₁ : F)
    (h₀ : x₀ ≠ 0) (h₁ : x₁ ≠ 0)
    (h_x₀_add : 1 + x₀ ≠ 0)
    (h_x₁_add : 1 + x₁ ≠ 0)
    (h_sum : 1 + x₀ + x₁ ≠ 0) :
    let x₂ := (1 + x₁) / x₀
    let x₃ := (1 + x₂) / x₁
    let x₄ := (1 + x₃) / x₂
    let x₅ := (1 + x₄) / x₃
    let x₆ := (1 + x₅) / x₄
    x₅ = x₀ ∧ x₆ = x₁ := by
  sorry

end PlabicPureBraidMapping
