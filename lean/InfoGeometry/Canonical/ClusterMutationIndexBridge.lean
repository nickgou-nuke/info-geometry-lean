import Mathlib.Tactic
import Mathlib.Logic.Relation

/-!
# Integer count identities for bipartite graph data

`PlabicCounts` contains only three integers. The update functions below are
count-level models and do not carry or transform a plabic graph. Their proofs
establish arithmetic invariance of the stated expressions under those updates;
they do not prove mutation invariance of an actual graph invariant or identify
`helicityDefect` with a physical helicity or a Dirac index.
-/

namespace PlabicAmplituhedron

structure PlabicCounts where
  V_black : ℤ
  V_white : ℤ
  E_internal : ℤ
  deriving Repr, DecidableEq

def kGrassmannian (p : PlabicCounts) : ℤ :=
  2 * p.V_black + p.V_white - p.E_internal

def nExternal (p : PlabicCounts) : ℤ :=
  3 * (p.V_black + p.V_white) - 2 * p.E_internal

def helicityDefect (p : PlabicCounts) : ℤ :=
  p.V_black - p.V_white

theorem helicityDefect_eq_two_k_sub_next (p : PlabicCounts) :
    helicityDefect p = 2 * kGrassmannian p - nExternal p := by
  dsimp [helicityDefect, kGrassmannian, nExternal]; ring

theorem two_k_eq_next_add_helicityDefect (p : PlabicCounts) :
    2 * kGrassmannian p = nExternal p + helicityDefect p := by
  dsimp [helicityDefect, kGrassmannian, nExternal]; ring

def applySquareMove (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black - 2 + 2
    V_white := p.V_white - 2 + 2
    E_internal := p.E_internal - 4 + 4 }

theorem k_invariant_square_move (p : PlabicCounts) :
    kGrassmannian (applySquareMove p) = kGrassmannian p := by
  dsimp [applySquareMove, kGrassmannian]; ring

theorem next_invariant_square_move (p : PlabicCounts) :
    nExternal (applySquareMove p) = nExternal p := by
  dsimp [applySquareMove, nExternal]; ring

theorem helicityDefect_invariant_square_move (p : PlabicCounts) :
    helicityDefect (applySquareMove p) = helicityDefect p := by
  dsimp [applySquareMove, helicityDefect]; ring

def applyBubbleReduction (p : PlabicCounts) : PlabicCounts :=
  { V_black := p.V_black - 1
    V_white := p.V_white - 1
    E_internal := p.E_internal - 3 }

theorem k_invariant_bubble_reduction (p : PlabicCounts) :
    kGrassmannian (applyBubbleReduction p) = kGrassmannian p := by
  dsimp [applyBubbleReduction, kGrassmannian]; ring

theorem next_invariant_bubble_reduction (p : PlabicCounts) :
    nExternal (applyBubbleReduction p) = nExternal p := by
  dsimp [applyBubbleReduction, nExternal]; ring

theorem helicityDefect_invariant_bubble_reduction (p : PlabicCounts) :
    helicityDefect (applyBubbleReduction p) = helicityDefect p := by
  dsimp [applyBubbleReduction, helicityDefect]; ring

inductive ClusterMove : PlabicCounts → PlabicCounts → Prop where
  | squareMove (p : PlabicCounts) : ClusterMove p (applySquareMove p)
  | bubbleReduction (p : PlabicCounts) : ClusterMove p (applyBubbleReduction p)
  | bubbleCreation (p : PlabicCounts) : ClusterMove (applyBubbleReduction p) p

theorem k_invariant_of_cluster_move {p p' : PlabicCounts} (h : ClusterMove p p') :
    kGrassmannian p' = kGrassmannian p := by
  cases h
  case squareMove => exact k_invariant_square_move p
  case bubbleReduction => exact k_invariant_bubble_reduction p
  case bubbleCreation => exact (k_invariant_bubble_reduction p').symm

theorem next_invariant_of_cluster_move {p p' : PlabicCounts} (h : ClusterMove p p') :
    nExternal p' = nExternal p := by
  cases h
  case squareMove => exact next_invariant_square_move p
  case bubbleReduction => exact next_invariant_bubble_reduction p
  case bubbleCreation => exact (next_invariant_bubble_reduction p').symm

theorem helicityDefect_invariant_of_cluster_move {p p' : PlabicCounts} (h : ClusterMove p p') :
    helicityDefect p' = helicityDefect p := by
  cases h
  case squareMove => exact helicityDefect_invariant_square_move p
  case bubbleReduction => exact helicityDefect_invariant_bubble_reduction p
  case bubbleCreation => exact (helicityDefect_invariant_bubble_reduction p').symm

def ClusterEquiv (p p' : PlabicCounts) : Prop :=
  Relation.ReflTransGen ClusterMove p p'

theorem k_invariant_of_cluster_equiv {p p' : PlabicCounts} (h : ClusterEquiv p p') :
    kGrassmannian p' = kGrassmannian p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [k_invariant_of_cluster_move hstep, ih]

theorem next_invariant_of_cluster_equiv {p p' : PlabicCounts} (h : ClusterEquiv p p') :
    nExternal p' = nExternal p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [next_invariant_of_cluster_move hstep, ih]

theorem helicityDefect_invariant_of_cluster_equiv {p p' : PlabicCounts} (h : ClusterEquiv p p') :
    helicityDefect p' = helicityDefect p := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [helicityDefect_invariant_of_cluster_move hstep, ih]

structure LocalMutation where
  delta_V_black : ℤ
  delta_V_white : ℤ
  delta_E_internal : ℤ

def PreservesK (m : LocalMutation) : Prop :=
  2 * m.delta_V_black + m.delta_V_white - m.delta_E_internal = 0

def PreservesNext (m : LocalMutation) : Prop :=
  3 * (m.delta_V_black + m.delta_V_white) - 2 * m.delta_E_internal = 0

def PreservesHelicityDefect (m : LocalMutation) : Prop :=
  m.delta_V_black - m.delta_V_white = 0

theorem preservesK_iff_preservesHelicityDefect (m : LocalMutation) (h_next : PreservesNext m) :
    PreservesK m ↔ PreservesHelicityDefect m := by
  dsimp [PreservesK, PreservesNext, PreservesHelicityDefect] at *
  omega

end PlabicAmplituhedron
