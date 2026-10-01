import Mathlib.Tactic

import InfoGeometry.Canonical.ChiralBipartiteDiracNetworkBridge
import InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

/-!
# Plabic count index and cluster-move invariance

This module formalizes the exact combinatorial identity behind the proposed
plabic/network index bridge.

For trivalent on-shell counts one has

  k = 2 V_black + V_white - E_internal

and the external-leg balance

  n = 3 (V_black + V_white) - 2 E_internal.

Only with the second relation does the algebraic identity

  2 k - n = V_black - V_white

follow.

Square moves preserve the count data.  A black-white bubble reduction changes

  Delta V_black = -1,
  Delta V_white = -1,
  Delta E_internal = -3,
  Delta n = 0,

and therefore preserves k, V_black - V_white, and the trivalent balance.

No theorem here identifies this combinatorial integer with a Fredholm index,
Witten index, or grading trace without an explicit comparison hypothesis.
-/

namespace InfoGeometry.Canonical.ClusterMutationIndexBridge

/-- Integer count model for a finite trivalent bipartite on-shell graph. -/
structure PlabicCounts where
  Vblack : ℤ
  Vwhite : ℤ
  Eint : ℤ
  next : ℤ
  trivalentBalance :
    next = 3 * (Vblack + Vwhite) - 2 * Eint

namespace PlabicCounts

/-- Grassmannian helicity degree. -/
def k (s : PlabicCounts) : ℤ :=
  2 * s.Vblack + s.Vwhite - s.Eint

/-- Bipartite color-count index. -/
def colorIndex (s : PlabicCounts) : ℤ :=
  s.Vblack - s.Vwhite

/-- Helicity defect. -/
def helicityDefect (s : PlabicCounts) : ℤ :=
  2 * s.k - s.next

/-- Under the trivalent external-leg balance, the helicity defect equals the
black-minus-white count exactly. -/
theorem helicityDefect_eq_colorIndex (s : PlabicCounts) :
    s.helicityDefect = s.colorIndex := by
  unfold helicityDefect k colorIndex
  rw [s.trivalentBalance]
  ring

/-- Square/urban-renewal count move.  At the level relevant to these
invariants, the counts are unchanged. -/
def squareMove (s : PlabicCounts) : PlabicCounts :=
  s

@[simp] theorem squareMove_k (s : PlabicCounts) :
    (s.squareMove).k = s.k := rfl

@[simp] theorem squareMove_colorIndex (s : PlabicCounts) :
    (s.squareMove).colorIndex = s.colorIndex := rfl

@[simp] theorem squareMove_helicityDefect (s : PlabicCounts) :
    (s.squareMove).helicityDefect = s.helicityDefect := rfl

/-- Bubble reduction removes one black vertex, one white vertex, and three
internal edges, with the external-leg count unchanged. -/
def bubbleReduction (s : PlabicCounts) : PlabicCounts where
  Vblack := s.Vblack - 1
  Vwhite := s.Vwhite - 1
  Eint := s.Eint - 3
  next := s.next
  trivalentBalance := by
    rw [s.trivalentBalance]
    ring

theorem bubbleReduction_k (s : PlabicCounts) :
    (s.bubbleReduction).k = s.k := by
  unfold bubbleReduction k
  ring

theorem bubbleReduction_colorIndex (s : PlabicCounts) :
    (s.bubbleReduction).colorIndex = s.colorIndex := by
  unfold bubbleReduction colorIndex
  ring

theorem bubbleReduction_helicityDefect (s : PlabicCounts) :
    (s.bubbleReduction).helicityDefect = s.helicityDefect := by
  rw [helicityDefect_eq_colorIndex, helicityDefect_eq_colorIndex,
    bubbleReduction_colorIndex]

/-- The exact cluster-move invariant packet. -/
theorem cluster_move_invariant_packet (s : PlabicCounts) :
    (s.squareMove).k = s.k ∧
    (s.squareMove).colorIndex = s.colorIndex ∧
    (s.bubbleReduction).k = s.k ∧
    (s.bubbleReduction).colorIndex = s.colorIndex := by
  exact ⟨squareMove_k s, squareMove_colorIndex s,
    bubbleReduction_k s, bubbleReduction_colorIndex s⟩

/-- The numerical k=1,n=1 sector has helicity defect +1.  This is an
arithmetic statement only; no zero-mode existence is inferred. -/
theorem fundamental_sector_defect
    (s : PlabicCounts)
    (hk : s.k = 1)
    (hn : s.next = 1) :
    s.helicityDefect = 1 := by
  unfold helicityDefect
  rw [hk, hn]
  norm_num

/-- Consequently the color-count index is +1 in that sector. -/
theorem fundamental_sector_colorIndex
    (s : PlabicCounts)
    (hk : s.k = 1)
    (hn : s.next = 1) :
    s.colorIndex = 1 := by
  rw [← helicityDefect_eq_colorIndex s]
  exact fundamental_sector_defect s hk hn

/-! ## Explicit comparison sockets -/

/-- Conditional Fredholm comparison: if a supplied Fredholm index is known to
equal the combinatorial color index, then it also equals the helicity defect. -/
theorem fredholmIndex_eq_helicityDefect_of_identification
    (s : PlabicCounts)
    (fredholmIndex : ℤ)
    (hFredholm : fredholmIndex = s.colorIndex) :
    fredholmIndex = s.helicityDefect := by
  rw [hFredholm, helicityDefect_eq_colorIndex]

/-- Conditional Witten comparison. -/
theorem wittenIndex_eq_helicityDefect_of_identification
    (s : PlabicCounts)
    (wittenIndex : ℤ)
    (hWitten : wittenIndex = s.colorIndex) :
    wittenIndex = s.helicityDefect := by
  rw [hWitten, helicityDefect_eq_colorIndex]

/-- Conditional grading/parity trace comparison. -/
theorem gradingTrace_eq_helicityDefect_of_identification
    (s : PlabicCounts)
    (gradingTrace : ℤ)
    (hTrace : gradingTrace = s.colorIndex) :
    gradingTrace = s.helicityDefect := by
  rw [hTrace, helicityDefect_eq_colorIndex]

/-- Four-way equality once all three independent identifications are supplied
explicitly. -/
theorem unified_index_packet_of_identifications
    (s : PlabicCounts)
    (fredholmIndex wittenIndex gradingTrace : ℤ)
    (hFredholm : fredholmIndex = s.colorIndex)
    (hWitten : wittenIndex = s.colorIndex)
    (hTrace : gradingTrace = s.colorIndex) :
    s.helicityDefect = s.colorIndex ∧
    fredholmIndex = s.colorIndex ∧
    wittenIndex = s.colorIndex ∧
    gradingTrace = s.colorIndex := by
  exact ⟨helicityDefect_eq_colorIndex s, hFredholm, hWitten, hTrace⟩

end PlabicCounts

end InfoGeometry.Canonical.ClusterMutationIndexBridge
