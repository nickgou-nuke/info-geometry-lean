
import Mathlib.Logic.Relation
import Mathlib.Tactic

open Relation

namespace PlabicPureBraidMapping

/-! This module proves invariance of the displayed integer count formulas under
the declared count updates, and a field-valued pentagon recurrence. It does not
construct plabic graphs, a cluster mutation action, or a pure braid
representation; those geometric inputs remain a separate development target. -/

/-! ### 1. Integer count expressions -/

/-- A triple of integer counts. No graph or incidence structure is carried. -/
structure PlabicCounts where
  V_black : ℤ
  V_white : ℤ
  E_internal : ℤ
  deriving Repr, DecidableEq

/-- The integer expression conventionally assigned to `k`. -/
def kGrassmannian (p : PlabicCounts) : ℤ :=
  2 * p.V_black + p.V_white - p.E_internal

/-- The integer expression conventionally assigned to the external count. -/
def nExternal (p : PlabicCounts) : ℤ :=
  3 * (p.V_black + p.V_white) - 2 * p.E_internal

/-- The difference between the two vertex-count coordinates. -/
def helicityDefect (p : PlabicCounts) : ℤ :=
  p.V_black - p.V_white

/-! ### 2. Count-level transformations -/

/-- Count update named for a square move; no graph move is constructed. -/
def applySquareMove (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black - 2 + 2
    V_white := p.V_white - 2 + 2
    E_internal := p.E_internal - 4 + 4 }

/-- Count update named for bubble reduction; no graph move is constructed. -/
def applyBubbleRed (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black - 1
    V_white := p.V_white - 1
    E_internal := p.E_internal - 3 }

/-- Count update named for bubble creation; no graph move is constructed. -/
def applyBubbleCre (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black + 1
    V_white := p.V_white + 1
    E_internal := p.E_internal + 3 }

/-- One of the declared count updates. -/
inductive AtomicClusterMove : PlabicCounts → PlabicCounts → Prop where
  | square (p : PlabicCounts) : AtomicClusterMove p (applySquareMove p)
  | bubbleRed (p : PlabicCounts) : AtomicClusterMove p (applyBubbleRed p)
  | bubbleCre (p : PlabicCounts) : AtomicClusterMove p (applyBubbleCre p)

/-- Reflexive-transitive closure of the declared count updates. -/
def ClusterEquiv (p p' : PlabicCounts) : Prop :=
  ReflTransGen AtomicClusterMove p p'

/-! ### 3. Invariance of count expressions under count updates -/

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
  let x2 := (1 + x₁) / x₀
  let x3 := (1 + x2) / x₁
  let x4 := (1 + x3) / x2
  let x5 := (1 + x4) / x3
  let x6 := (1 + x5) / x4
  change x5 = x₀ ∧ x6 = x₁
  have hsum' : 1 + x₁ + x₀ ≠ 0 := by
    convert h_sum using 1
    ring
  have hx3 : x3 = (1 + x₀ + x₁) / (x₀ * x₁) := by
    change (1 + (1 + x₁) / x₀) / x₁ = _
    field_simp [h₀, h₁]
    ring
  have hx4 : x4 = (1 + x₀) / x₁ := by
    change (1 + x3) / ((1 + x₁) / x₀) = _
    rw [hx3]
    field_simp [h₀, h₁, h_x₁_add]
    ring
  have hx5 : x5 = x₀ := by
    change (1 + x4) / x3 = _
    rw [hx4, hx3]
    field_simp [h₀, h₁, hsum']
    ring
  have hx6 : x6 = x₁ := by
    change (1 + x5) / x4 = _
    rw [hx5, hx4]
    field_simp [h₀, h₁, h_x₀_add]
  exact ⟨hx5, hx6⟩

end PlabicPureBraidMapping
